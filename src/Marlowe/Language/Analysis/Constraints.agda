{-
  models constraints on variables and accounts.
  Allows for merging of these constraints, as is needed for sequential composition.
-}
{-# OPTIONS --erasure --erased-matches #-}

open import Relation.Binary using (DecidableEquality)

module Marlowe.Language.Analysis.Constraints
  {Party : Set}
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where

open import Haskell.Prelude
pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []

open import Marlowe.Language using (Contract; Token)

{-
postulate instance Eq-ByteString : Eq ByteString
instance
  Eq-ValueId : Eq ValueId
  Eq-ValueId = record { _==_ = λ (mkValueId b₁) (mkValueId b₂) → b₁ == b₂ }
-}

postulate
  instance Eq-Token : Eq Token
  instance Eq-AccountId : Eq AccountId
import Relation.Binary.PropositionalEquality as Eq

-- Constraints are just boolean expressions, so for now they can
-- be synonyms for Observations. We might want to make them symbolic later?
Constraint = Observation
postulate
  allAccountsEmpty : Constraint
  
-- We need a special Constraint for when things are impossible.
postulate
  Defined : ValueId → Constraint
  NotDefined : ValueId → Constraint

Constraints = List Constraint

data Update : Set where
  Assign : ValueId → Value → Update
  Constrain : Constraint → Update
  Account : AccountId → Token → Value → Update
{-# COMPILE AGDA2HS Update #-}

Updates = List Update

data Output : Set where
  PayOut : Payee → Token → Value → Output
  WarningNonPositivePay : Output
  WarningPartialPay : Output
  WarningNonPositiveDeposit : Output
  WarningShadowing : Output
  WarningAssertionFailed : Output
  WarningUnreachable : Output
  WarningFundsOnClose : Output
{-# COMPILE AGDA2HS Output #-}

Outputs = List Output

postulate
  constraintFromObs : Observation → Constraint
  constraintFromPay : AccountId → Token → Value → Constraint
  obsToConstraint : Observation → Constraint
  minTimeConstraint : Timeout → Constraint
  z3prove : Constraints → Constraints → Bool -- Ask z3 if one set of constraints _implies_ the other
  z3sat : Constraints → Bool -- For now, lets just ask if it _can_ be satisfied

-- Merge constraints.
-- This is to be used when composing steps, so if the previous constraints imply the
-- new constraints they can be skipped/absorbed, but if not then they need to be added.
-- If the result is unsatisfiable then we can return False and stop (although we ought to mention
-- that this path is unreachable)
constraintOverriding : Constraints → Constraints → Constraints
constraintOverriding (FalseObs ∷ _) _ = [ FalseObs ] -- False ruins everything
constraintOverriding _ (FalseObs ∷ _) = [ FalseObs ]
constraintOverriding cs [] = cs
constraintOverriding cs (nc ∷ ncs) =
      if z3prove cs [ nc ]
      then constraintOverriding cs ncs
      else let cs' = (cs ++ [ nc ]) in
        if z3sat cs'
        then constraintOverriding cs' ncs
        else [ FalseObs ]
{-# COMPILE AGDA2HS constraintOverriding #-}

syntax constraintOverriding x y =  x ⊕ᶜ y 

-- When one set of updates follows another we need to think about what they do overall
updateOverriding : Updates → Updates → Updates
updateOverriding u [] = u
updateOverriding [] u' = u'
updateOverriding ((Assign v vl) ∷ us) ((Assign v' vl') ∷ us')  =
               if v == v'
               then ((Assign v vl') ∷ (updateOverriding us us'))
               else ((Assign v vl) ∷ (updateOverriding us ((Assign v' vl') ∷ us')))
updateOverriding u ((Constrain obs) ∷ us') = (updateOverriding ((Constrain obs) ∷ u) us') -- Constraints just all get added?
updateOverriding ((Account aid t v) ∷ us) ((Account aid' t' v') ∷ us') = 
              if (aid == aid') && (t == t')
              then ((Account aid t (AddValue v v')) ∷ (updateOverriding us us'))
              else (Account aid t v) ∷ (updateOverriding us ((Account aid' t' v') ∷ us') )
updateOverriding (u ∷ us) us' = u ∷ (updateOverriding us us') -- Otherwise just keep going
{-# COMPILE AGDA2HS updateOverriding #-}
syntax updateOverriding x y = x ⊕ᵤ y

postulate
  -- Calculate the precondition before an update to produce the Constraints after it
  -- e.g. [x := x - 100] ⊝ᵤ [x > 100] --> [x > 200]
  updatePreconditions : Updates → Constraints → Constraints
syntax updatePreconditions x y = x ⊝ᵤ y

ConstrainedStep = (Constraints × Updates × Outputs × Maybe Contract)

constrainSmallStep : Contract → List ConstrainedStep
constrainSmallStep Close = 
                   ([ allAccountsEmpty ] , [] , [] , Nothing)
                   ∷ ([ NotObs allAccountsEmpty ] , [] , [ WarningFundsOnClose ] , Nothing)
                   ∷ []
-- We need to be aware that Pay to an account is an internal transfer, whereas
-- Pay to a Party is an Output
constrainSmallStep (Pay aid (mkAccount payee) token value cont) = [ ( [ constraintFromPay aid token value ] ,  ((Account payee token value) ∷ (Account aid token (NegValue value)) ∷ []) , [] , Just cont) ] -- Internal transfer to an Account
constrainSmallStep (Pay aid (mkParty payee) token value cont) = [ ( [ constraintFromPay aid token value ] , ((Account (mkAccountId payee) token value) ∷ (Account aid token (NegValue value)) ∷ []) , [ PayOut (mkParty payee) token value ] , Just cont) ] -- Output payment
constrainSmallStep (If obs c₁ c₂) =
                   ([ constraintFromObs obs ] , [ Constrain (obsToConstraint obs) ] , [] , Just c₁)
                   ∷ ( [ constraintFromObs (NotObs obs) ] , [ Constrain (constraintFromObs (NotObs obs)) ] , [] , Just c₂)
                   ∷ []
constrainSmallStep (When cases timeout cont) = [] -- Small steps don't handle inputs 
constrainSmallStep (Let var val cont) =
                   ([ Defined var ] , [ Assign var val ] , [ WarningShadowing ] , Just cont) -- If the value is defined this still works but produces a Warning
                   ∷ ([ NotDefined var ] , [ Assign var val ] , [] , Just cont)
                   ∷ []
constrainSmallStep (Assert obs cont) =
                   ([ constraintFromObs obs ] , [] , [] , Just cont) -- Either this assertion is true
                    ∷ ([ constraintFromObs (NotObs obs) ] , [] , [ WarningAssertionFailed ] , Just cont) -- Or we need to emit a Warning
                    ∷ []
                    
{-# COMPILE AGDA2HS constrainSmallStep #-}

mergeSmallConstraints : ConstrainedStep → ConstrainedStep → ConstrainedStep
mergeSmallConstraints (constraints , updates , outputs , _) (c' , u' , o' , cont') =
                         (((updates ⊝ᵤ constraints) ⊕ᶜ c') , updates ⊕ᵤ u' , outputs ++ o' , cont')
{-# COMPILE AGDA2HS mergeSmallConstraints #-}

reduceSmallConstraintsInner : List ConstrainedStep → List ConstrainedStep
reduceSmallConstraintsInner [] = []
reduceSmallConstraintsInner ((constraints , updates , outputs , Nothing) ∷ css) = ((constraints , updates , outputs , Nothing) ∷ reduceSmallConstraintsInner css)
reduceSmallConstraintsInner ((constraints , updates , outputs , Just cont) ∷ css) =
                            let css' = constrainSmallStep cont in
                              (map (mergeSmallConstraints (constraints , updates , outputs , Just cont)) css')
                              ++ (reduceSmallConstraintsInner css)
{-# COMPILE AGDA2HS reduceSmallConstraintsInner #-}

reduceSmallConstraints : Contract → List ConstrainedStep
reduceSmallConstraints c = reduceSmallConstraintsInner (constrainSmallStep c)
{-# COMPILE AGDA2HS reduceSmallConstraints #-}

data Input : Set where
  inputDeposit : AccountId → Party → Token → Value → Input
  inputChoice : ChoiceId → List Marlowe.Language.Contract.Bound → Input
  inputNotify : Observation → Input
  inputNull : Input -- Null inputs happen on timeouts
  
ConstrainCase : ConstrainedStep → Case → (ConstrainedStep × Input × List ConstrainedStep)
ConstrainCase prefix (mkCase (Deposit aid party tok val) cont) =
                      (prefix , (inputDeposit aid party tok val) , reduceSmallConstraints cont)
ConstrainCase prefix (mkCase (Choice cid bounds) cont) =  (prefix , (inputChoice cid bounds) , reduceSmallConstraints cont)
ConstrainCase prefix (mkCase (Notify obs) cont) =  (prefix , (inputNotify obs) , reduceSmallConstraints cont)

makeTimeoutCase : ConstrainedStep → Timeout → Contract → (ConstrainedStep × Input × List ConstrainedStep)
makeTimeoutCase (pc , pu , po , pcont)  timeout cont =
                ( (pc ⊕ᶜ [ minTimeConstraint timeout ] , pu , po , pcont)
                , inputNull , reduceSmallConstraints cont)

{-# TERMINATING #-} -- I shouldn't need to use this :(
constrainMidConstraints : ConstrainedStep → Contract → List (ConstrainedStep × Input × List ConstrainedStep)
constrainMidConstraintsInner : ConstrainedStep → List ConstrainedStep → List (ConstrainedStep × Input × List ConstrainedStep)
constrainMidConstraintsInner _ [] = []
constrainMidConstraintsInner prefix ((c , o , u , Nothing) ∷ css)=
                             [ ((c , o , u , Nothing) , inputNull , []) ] ++ constrainMidConstraintsInner prefix css
constrainMidConstraintsInner prefix ((c , o , u , Just cont) ∷ css) =
                             let p = (c , o , u , Just cont) in
                               (constrainMidConstraints (mergeSmallConstraints prefix p) cont)
                                 ++ constrainMidConstraintsInner prefix css

constrainMidConstraints prefix Close = [(prefix , inputNull , [])]
constrainMidConstraints prefix (When cases timeout cont) =
                        (map (ConstrainCase prefix) cases) ++ [ (makeTimeoutCase prefix timeout cont) ]
constrainMidConstraints prefix c = 
                        let css = reduceSmallConstraints c in -- anything else will have some small-step prefix to consume first
                          constrainMidConstraintsInner prefix css
{-# COMPILE AGDA2HS constrainMidConstraints #-}

