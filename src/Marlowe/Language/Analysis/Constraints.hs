module Marlowe.Language.Analysis.Constraints where

import Marlowe.Core.Contract (AccountId(mkAccountId), Contract(Assert, Close, If, Let, Pay, When), Observation(FalseObs, NotObs), Payee(mkAccount, mkParty), Token, Value(AddValue, NegValue), ValueId)

data Update = Assign ValueId Value
            | Constrain Constraint
            | Account AccountId Token Value

data Output = PayOut Payee Token Value
            | WarningNonPositivePay
            | WarningPartialPay
            | WarningNonPositiveDeposit
            | WarningShadowing
            | WarningAssertionFailed
            | WarningUnreachable
            | WarningFundsOnClose

constraintOverriding :: Constraints -> Constraints -> Constraints
constraintOverriding (FalseObs : _) _ = [FalseObs]
constraintOverriding _ (FalseObs : _) = [FalseObs]
constraintOverriding cs [] = cs
constraintOverriding cs (nc : ncs)
  = if z3prove cs [nc] then constraintOverriding cs ncs else
      if z3sat (cs ++ [nc]) then constraintOverriding (cs ++ [nc]) ncs
        else [FalseObs]

updateOverriding :: Updates -> Updates -> Updates
updateOverriding u [] = u
updateOverriding [] u' = u'
updateOverriding (Assign v vl : us) (Assign v' vl' : us')
  = if v == v' then Assign v vl' : updateOverriding us us' else
      Assign v vl : updateOverriding us (Assign v' vl' : us')
updateOverriding u (Constrain obs : us')
  = updateOverriding (Constrain obs : u) us'
updateOverriding (Account aid t v : us) (Account aid' t' v' : us')
  = if aid == aid' && t == t' then
      Account aid t (AddValue v v') : updateOverriding us us' else
      Account aid t v : updateOverriding us (Account aid' t' v' : us')
updateOverriding (u : us) us' = u : updateOverriding us us'

constrainSmallStep :: Contract -> [ConstrainedStep]
constrainSmallStep Close
  = [([allAccountsEmpty], ([], []), Nothing),
     ([NotObs allAccountsEmpty], ([], [WarningFundsOnClose]), Nothing)]
constrainSmallStep (Pay aid (Account payee) token value cont)
  = [([constraintFromPay aid token value],
      ([Account payee token value, Account aid token (NegValue value)],
       []),
      Just cont)]
constrainSmallStep (Pay aid (Party payee) token value cont)
  = [([constraintFromPay aid token value],
      ([Account (mkAccountId payee) token value,
        Account aid token (NegValue value)],
       [PayOut (mkParty payee) token value]),
      Just cont)]
constrainSmallStep (If obs c₁ c₂)
  = [([constraintFromObs obs],
      ([Constrain (obsToConstraint obs)], []), Just c₁),
     ([constraintFromObs (NotObs obs)],
      ([Constrain (constraintFromObs (NotObs obs))], []), Just c₂)]
constrainSmallStep (When cases timeout cont) = []
constrainSmallStep (Let var val cont)
  = [([Defined var], ([Assign var val], [WarningShadowing]),
      Just cont),
     ([NotDefined var], ([Assign var val], []), Just cont)]
constrainSmallStep (Assert obs cont)
  = [([constraintFromObs obs], ([], []), Just cont),
     ([constraintFromObs (NotObs obs)], ([], [WarningAssertionFailed]),
      Just cont)]

mergeSmallConstraints ::
                      ConstrainedStep -> ConstrainedStep -> ConstrainedStep
mergeSmallConstraints (constraints, (updates, outputs), _)
  (c', (u', o'), cont')
  = (constraintOverriding (updates ⊝ᵤ constraints) c',
     (updateOverriding updates u', outputs ++ o'), cont')

reduceSmallConstraintsInner ::
                            [ConstrainedStep] -> [ConstrainedStep]
reduceSmallConstraintsInner [] = []
reduceSmallConstraintsInner
  ((constraints, (updates, outputs), Nothing) : css)
  = (constraints, (updates, outputs), Nothing) :
      reduceSmallConstraintsInner css
reduceSmallConstraintsInner
  ((constraints, (updates, outputs), Just cont) : css)
  = map
      (mergeSmallConstraints
         (constraints, (updates, outputs), Just cont))
      (constrainSmallStep cont)
      ++ reduceSmallConstraintsInner css

reduceSmallConstraints :: Contract -> [ConstrainedStep]
reduceSmallConstraints c
  = reduceSmallConstraintsInner (constrainSmallStep c)

constrainMidConstraints ::
                        ConstrainedStep ->
                          Contract -> [(ConstrainedStep, Input, [ConstrainedStep])]
constrainMidConstraints prefix Close = [(prefix, inputNull, [])]
constrainMidConstraints prefix (When cases timeout cont)
  = map (ConstrainCase prefix) cases ++
      [makeTimeoutCase prefix timeout cont]
constrainMidConstraints prefix c
  = constrainMidConstraintsInner prefix (reduceSmallConstraints c)

