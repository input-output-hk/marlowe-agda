module Marlowe.Semantics.Operate where

open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Integer using (_<?_; _≤?_; _≟_ ; _⊔_; _⊓_; _+_; _-_; +_; 0ℤ ; _≤_ ; _>_ ; _≥_ ; _<_; ∣_∣)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂)
import Data.String as String
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Reduce

open import Contrib.Data.List.AssocList hiding (_∈_)
open Decidable _≟-AccountId×Token_  renaming (_‼_default_ to _‼-AccountId×Token_default_; _↑_ to _↑-AccountId×Token_) hiding (_∈?_)
open Decidable _≟-ChoiceId_ renaming (_‼_default_ to _‼-ChoiceId_default_;  _↑_ to _↑-ChoiceId_) using (_∈?_)
open Decidable _≟-ValueId_ renaming (_‼_ to _‼_ValueId_; _‼_default_ to _‼-ValueId_default_; _∈?_ to _∈-ValueId?_; _↑_ to _↑-ValueId_)

open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

open Configuration
open State
open PosixTime
open TransactionInput

record Result : Set where
  constructor ⟦_,_,_⟧
  field
    warnings : List TransactionWarning
    payments : List Payment
    state : State


data _⊢_⇓_ : Environment → Contract × TransactionInput × State → Result → Set where

  ⇓-Deposit :
    ∀ {a} {p} {t} {tₛ Δₜ} {v} {n} {c} {cont} {is} {s} {r} {cases} {timeout}
    → (mkCase (Deposit a p t v) c) ∈ cases
    → ∣ ℰ⟦ v ⟧ (mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)) s ∣ ≡ n
    → (tₛ ℕ.+ Δₜ) ℕ.< timeout
    → mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) ⊢
      ( c
      , is
      , record s { accounts = ((a , t) , n) ↑-update (accounts s) }
      ) ⇓ r
    -------------------------------------------------------------------
    → mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) ⊢
      ( When cases (mkTimeout (mkPosixTime timeout)) cont
      , record is { inputs = NormalInput (IDeposit a p t n) ∷ inputs is }
      , s
      ) ⇓ r

  ⇓-Choice :
    ∀ {c} {cont} {i} {n} {s} {r} {is} {cs} {bs} {cases} {timeout} {e}
    → (mkCase (Choice i bs) c) ∈ cases
    → n inBounds bs ≡ true
    → e ⊢
      ( c
      , is
      , record s { choices = (i , unChosenNum n) ↑-ChoiceId cs }
      ) ⇓ r
    -----------------------------------------------------------------
    → e ⊢
      ( When cases timeout cont
      , record is { inputs = NormalInput (IChoice i n) ∷ inputs is }
      , s
      ) ⇓ r

  ⇓-Notify :
    ∀ {c} {cont} {is} {s} {r} {o} {e} {cases} {timeout}
    → (mkCase (Notify o) c) ∈ cases
    → 𝒪⟦ o ⟧ e s ≡ true
    → e ⊢
      ( c
      , is
      , s
      ) ⇓ r
    ---------------------------------------------------
    → e ⊢
      ( When cases timeout cont
      , record is { inputs = NormalInput INotify ∷ inputs is }
      , s
      ) ⇓ r

  ⇓-Close :
    ∀ {s} {i} {e}
    → inputs i ≡ []
    ------------------------
    → e ⊢
      (Close , i , s) ⇓
        ⟦ []
        , []
        , record s { accounts = [] }
        ⟧

  ⇓-Reduce-until-quiescent :
    ∀ {c₁ c₂} {i} {ws₁ ws₂} {s} {ps₁ ps₂}
    → c₁ ⇒ c₂
    → environment c₂ ⊢
      ( contract c₂
      , i
      , state c₂
      ) ⇓ ⟦ ws₂ , ps₂ , s ⟧
    -----------------
    → environment c₁ ⊢
      ( contract c₁
      , i
      , state c₁
      ) ⇓ ⟦ ws₁ , ps₁ , s ⟧



private

  timeout : PosixTime
  timeout = mkPosixTime 100

  p₁ : Party
  p₁ = Role (mkByteString "role1")

  p₂ : Party
  p₂ = Role (mkByteString "role2")

  a₁ : AccountId
  a₁ = mkAccountId p₁

  a₂ : AccountId
  a₂ = mkAccountId p₂

  t : Token
  t = mkToken (mkByteString "") (mkByteString "")

  v : Value
  v = Constant (+ 1)

  d : Contract
  d = When ([ mkCase (Deposit a₁ p₂ t v) Close ]) (mkTimeout timeout) Close

  c : Contract
  c = Assert TrueObs d

  s : State
  s = emptyState (mkPosixTime 0)

  i : TransactionInput
  i = mkTransactionInput (mkInterval (mkPosixTime 0) 10) [ NormalInput (IDeposit a₁ p₂ t 1) ]

  e : Environment
  e = mkEnvironment (mkInterval (mkPosixTime 0) 2)

  reduction-steps :
    e ⊢ (c , i , s)
    ⇓ ⟦ []
      , [ a₁ [ t , 1 ]↦ mkParty p₁ ]
      , s
      ⟧
  reduction-steps =
    ⇓-Reduce-until-quiescent
      (reduce-until-quiescent ((⟪ c , s , e , [] , [] ⟫) ⇀⟨ AssertTrue refl ⟩ (⟪ d , s , e , [] , [] ⟫) ∎) (waiting (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))))
      (⇓-Deposit (here refl) refl (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
        (⇓-Close refl))


{-
⇓-deterministic :
  ∀ {C : Contract} {i : TransactionInput} {s : State} {D D′ : Result}
  → (C , i , s) ⇓ D
  → (C , i , s) ⇓ D′
  → D ≡ D′
⇓-deterministic (⇓-Deposit x x₁ x₂) (⇓-Deposit x₃ x₄ y) = {!!}
⇓-deterministic (⇓-Choice x x₁ x₂) (⇓-Choice y y₁ y₂) = {!!}
⇓-deterministic (⇓-Notify x x₁ x₂) (⇓-Notify y y₁ y₂) = {!!}
⇓-deterministic {C} {i} {s} (⇓-Close {s} {i} x) (⇓-Close {s} {i} y) = refl
-}
{-

fixInterval : TimeInterval → State → IntervalResult
fixInterval interval state =
  let
    mkInterval (mkPosixTime low) delta = interval
    high = low ℕ.+ delta
  in
    if high ℕ.<ᵇ low
      then mkIntervalError (InvalidInterval interval)
      else
        let
          curMinTime = State.minTime state
          newLow = low ℕ.⊔ PosixTime.getPosixTime curMinTime
          curInterval = record interval {startTime = mkPosixTime newLow}
          env = record {timeInterval = curInterval}
          newState = record state {minTime = mkPosixTime newLow}
        in
          if high ℕ.<ᵇ PosixTime.getPosixTime curMinTime
            then mkIntervalError (IntervalInPastError curMinTime interval)
            else IntervalTrimmed env newState

data ReduceEffect : Set where
  ReduceWithPayment : Payment → ReduceEffect
  ReduceNoPayment : ReduceEffect

data ReduceResult : Set where
  ContractQuiescent : Bool → List ReduceWarning → List Payment → State → Contract → ReduceResult
  RRAmbiguousTimeIntervalError : ReduceResult

reduceContractUntilQuiescent : Environment → State → Contract → ReduceResult
reduceContractUntilQuiescent e s c =
  let c = record {contract = c; state = s; environment = e; warnings = []; payments = []}
  in reductionSteps (eval c 100) -- TODO: how many steps...?
    where
      open Configuration
      reductionSteps : ∀ {c : Configuration} → QuiescentOrError c → ReduceResult
      -- reductionSteps (steps {d} x) = ContractQuiescent true (warnings d) (payments d) (state d) (contract d)
      reductionSteps ambiguousTimeInterval = RRAmbiguousTimeIntervalError
      reductionSteps {c} done = ContractQuiescent false (warnings c) (payments c) (state c) (contract c)

data ApplyWarning : Set where
  ApplyNoWarning : ApplyWarning
  ApplyNonPositiveDeposit : Party → AccountId → Token → Int → ApplyWarning

data ApplyAction : Set where
  AppliedAction : ApplyWarning → State → ApplyAction
  NotAppliedAction : ApplyAction

applyAction : Environment → State → InputContent → Action → ApplyAction
applyAction env state (IDeposit accId1 party1 tok1 amount) (Deposit accId2 party2 tok2 val) =
  if ⌊ accId1 ≟-AccountId accId2 ⌋ ∧ ⌊ party1 ≟-Party party2 ⌋ ∧ ⌊ tok1 ≟-Token tok2 ⌋ ∧ ⌊ ((+ amount) ≟ ℰ⟦ val ⟧ env state) ⌋
    then AppliedAction
           ApplyNoWarning (
             record state {
               accounts =
                 let i = (accId1 , tok1) ‼-AccountId×Token (State.accounts state) default 0
                 in ((accId1 , tok1) , i ℕ.+ amount) ↑-AccountId×Token (State.accounts state)
             })
    else NotAppliedAction
applyAction _ state (IChoice choId1 choice) (Choice choId2 bounds) =
  if ⌊ choId1 ≟-ChoiceId choId2 ⌋ ∧ choice inBounds bounds
    then AppliedAction ApplyNoWarning (record state {choices = (choId1 , unChosenNum choice) ↑-ChoiceId (State.choices state)})
    else NotAppliedAction
applyAction env state INotify (Notify obs) =
  if 𝒪⟦ obs ⟧ env state
    then AppliedAction ApplyNoWarning state
    else NotAppliedAction
applyAction _ _ _ _ = NotAppliedAction

getContinuation : Input → Case → Maybe Contract
getContinuation (NormalInput _) (mkCase _ continuation) = just continuation

data ApplyResult : Set where
  Applied : ApplyWarning → State → Contract → ApplyResult
  ApplyNoMatchError : ApplyResult
  ApplyHashMismatch : ApplyResult

applyCases : Environment → State → Input → List Case → ApplyResult
applyCases env state input (headCase ∷ tailCase)
  with applyAction env state (getInputContent input) (getAction headCase) | getContinuation input headCase
... | NotAppliedAction               | _                 = applyCases env state input tailCase
... | AppliedAction warning newState | just continuation = Applied warning newState continuation
... | _                              | nothing           = ApplyHashMismatch
applyCases _ _ _ [] = ApplyNoMatchError

applyInput : Environment → State → Input → Contract → ApplyResult
applyInput env state input (When cases _ _) = applyCases env state input cases
applyInput _ _ _ _ = ApplyNoMatchError

convertReduceWarnings : List ReduceWarning -> List TransactionWarning
convertReduceWarnings =
  foldr convertReduceWarning []
    where
      convertReduceWarning : ReduceWarning → List TransactionWarning → List TransactionWarning
      convertReduceWarning (ReduceNonPositivePay accId payee tok amount) acc = TransactionNonPositivePay accId payee tok amount ∷ acc
      convertReduceWarning (ReducePartialPay accId payee tok paid expected) acc = TransactionPartialPay accId payee tok paid expected ∷ acc
      convertReduceWarning (ReduceShadowing valId oldVal newVal) acc = TransactionShadowing valId oldVal newVal ∷ acc
      convertReduceWarning ReduceAssertionFailed acc = TransactionAssertionFailed ∷ acc

data ApplyAllResult : Set where
  ApplyAllSuccess : Bool → List TransactionWarning → List Payment → State → Contract → ApplyAllResult
  ApplyAllNoMatchError : ApplyAllResult
  ApplyAllAmbiguousTimeIntervalError : ApplyAllResult
  ApplyAllHashMismatch : ApplyAllResult

applyAllInputs : Environment → State → Contract → List Input → ApplyAllResult
applyAllInputs env state contract inputs =
  applyAllLoop false env state contract inputs [] []
    where
      convertApplyWarning : ApplyWarning -> List TransactionWarning
      convertApplyWarning (ApplyNoWarning) = []
      convertApplyWarning (ApplyNonPositiveDeposit party accId tok amount) =
        TransactionNonPositiveDeposit party accId tok amount ∷ []
      applyAllLoop : Bool → Environment → State → Contract → List Input → List TransactionWarning → List Payment → ApplyAllResult
      applyAllLoop contractChanged env state contract inputs warnings payments
        with reduceContractUntilQuiescent env state contract | inputs
      ... | RRAmbiguousTimeIntervalError | _ = ApplyAllAmbiguousTimeIntervalError
      ... | ContractQuiescent reduced reduceWarns pays curState cont | [] =
              ApplyAllSuccess (contractChanged ∨ reduced) (warnings ++ convertReduceWarnings reduceWarns) (payments ++ pays) curState cont
      ... | ContractQuiescent reduced reduceWarns pays curState cont | input  ∷ rest
              with applyInput env curState input cont
      ...       | Applied applyWarn newState cont =
                    applyAllLoop true env newState cont rest (warnings ++ convertReduceWarnings reduceWarns ++ convertApplyWarning applyWarn) (payments ++ pays)
      ...       | ApplyNoMatchError = ApplyAllNoMatchError
      ...       | ApplyHashMismatch = ApplyAllHashMismatch

isClose : Contract → Bool
isClose Close = true
isClose _     = false

notClose : Contract → Bool
notClose Close = false
notClose _     = true

computeTransaction : TransactionInput → State → Contract → TransactionOutput
computeTransaction (mkTransactionInput txInterval txInput) state contract
  with fixInterval txInterval state
... | mkIntervalError error = mkError (TEIntervalError error)
... | IntervalTrimmed env fixState with applyAllInputs env fixState contract txInput
... |   ApplyAllNoMatchError = mkError TEApplyNoMatchError
... |   ApplyAllAmbiguousTimeIntervalError = mkError TEAmbiguousTimeIntervalError
... |   ApplyAllHashMismatch = mkError TEHashMismatch
... |   ApplyAllSuccess reduced warnings payments newState cont =
          if not reduced ∧ (notClose contract ∨ null (State.accounts state))
            then mkError TEUselessTransaction
            else mkTransactionOutput warnings payments newState cont

playTraceAux : TransactionOutput → List TransactionInput → TransactionOutput
playTraceAux res [] = res
playTraceAux (mkTransactionOutput warnings payments state contract) (h ∷ t)
  with computeTransaction h state contract
... | mkTransactionOutput warnings' payments' state' contract' =
       playTraceAux (mkTransactionOutput (warnings ++ warnings') (payments ++ payments') state' contract') t
... | mkError error = mkError error
playTraceAux (mkError error) _ = mkError error

playTrace : PosixTime → Contract → List TransactionInput → TransactionOutput
playTrace minTime c = playTraceAux (mkTransactionOutput [] [] (emptyState minTime) c)

-}
