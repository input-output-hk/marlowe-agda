
module Marlowe.Semantics.Operate where


open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Integer using (_<?_; _≤?_; _≟_ ; _⊔_; _⊓_; _-_; 0ℤ ; _≤_ ; _>_ ; _≥_ ; _<_)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂)
import Data.String as String
open import Function.Base using (case_of_)
open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Primitives
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

open import Primitives
open Decidable _eqAccountIdTokenDec_  renaming (_‼_default_ to _‼ᵃ_default_) hiding (_∈?_)
open Decidable _eqChoiceId_ renaming (_‼_default_ to _‼ᶜ_default_) using (_∈?_)
open Decidable _eqValueId_ renaming (_‼_ to _‼ᵛ_; _‼_default_ to _‼ᵛ_default_; _∈?_ to _∈ᵛ?_)


fixInterval : TimeInterval → State → IntervalResult
fixInterval interval state =
  let
    (mkPosixTime low) , (mkPosixTime high) = interval
  in
    if ⌊ high <? low ⌋
      then mkIntervalError (InvalidInterval interval)
      else
        let
          curMinTime = State.minTime state
          newLow = low ⊔ PosixTime.getPosixTime curMinTime
          curInterval = record interval {fst = mkPosixTime newLow}
          env = record {timeInterval = curInterval}
          newState = record state {minTime = mkPosixTime newLow}
        in
          if ⌊ high <? PosixTime.getPosixTime curMinTime ⌋
            then mkIntervalError (IntervalInPastError curMinTime interval)
            else IntervalTrimmed env newState


refundOne : AssocList (AccountId × Token) Int → Maybe (Party × Token × Int × Accounts)
refundOne [] = nothing
refundOne (((mkAccountId ρ , τ) , ι) ∷ α) =
  if ⌊ ι ≤? 0ℤ ⌋
    then refundOne α
    else just (ρ , τ , ι , α)


moneyInAccount : AccountId → Token → Accounts → Int
moneyInAccount αₓ τ α = (αₓ , τ) ‼ᵃ α default 0ℤ

updateMoneyInAccount : AccountId → Token → Int → Accounts → Accounts
updateMoneyInAccount account token amount accounts =
  let
    key = account , token
  in
    if ⌊ amount ≤? 0ℤ ⌋
      then key ↓ accounts
      else ((key , amount) ↑ accounts)

addMoneyToAccount : AccountId → Token → Int → Accounts → Accounts
addMoneyToAccount account token amount accounts =
  let
    balance = moneyInAccount account token accounts
    newBalance = balance Data.Integer.+ amount
  in
    if ⌊ amount ≤? 0ℤ ⌋
      then accounts
      else updateMoneyInAccount account token newBalance accounts


data ReduceEffect : Set where
  ReduceWithPayment : Payment → ReduceEffect
  ReduceNoPayment : ReduceEffect

data ReduceWarning : Set where
  ReduceNoWarning : ReduceWarning
  ReduceNonPositivePay : AccountId → Payee → Token → Int → ReduceWarning
  ReducePartialPay : AccountId → Payee → Token → Int → Int → ReduceWarning
  ReduceShadowing : ValueId → Int → Int → ReduceWarning
  ReduceAssertionFailed : ReduceWarning

data ReduceStepResult : Set where
  Reduced : ReduceWarning → ReduceEffect → State → Contract → ReduceStepResult
  NotReduced : ReduceStepResult
  AmbiguousTimeIntervalReductionError : ReduceStepResult

data ReduceResult : Set where
  ContractQuiescent : Bool → List ReduceWarning → List Payment → State → Contract → ReduceResult
  RRAmbiguousTimeIntervalError : ReduceResult


giveMoney : AccountId → Payee → Token → Int → Accounts → ReduceEffect × Accounts
giveMoney account payee token amount accounts =
  record {fst = ReduceWithPayment (mkPayment account payee token amount); snd = newAccounts payee}
    where
      newAccounts : Payee → Accounts
      newAccounts payee' with payee'
      ... | mkParty _ = accounts
      ... | mkAccount account' = addMoneyToAccount account' token amount accounts


reduceContractStep : Environment → State → Contract → ReduceStepResult
reduceContractStep env state Close
  with refundOne (State.accounts state)
... | just (party , token , amount , newAccounts) =
       let
         newState = record state {accounts = newAccounts}
       in
         Reduced ReduceNoWarning (ReduceWithPayment (mkPayment (mkAccountId party) (mkParty party) token amount)) newState Close
... | nothing = NotReduced
reduceContractStep env state (Pay accId payee tok val cont) =
  let
    amountToPay = ℰ⟦ val ⟧ env state
  in
    if ⌊ amountToPay ≤? 0ℤ ⌋
      then (
        let
          warning = ReduceNonPositivePay accId payee tok amountToPay
        in
          Reduced warning ReduceNoPayment state cont
      )
      else (
        let
          balance = moneyInAccount accId tok (State.accounts state)
          paidAmount = balance ⊓ amountToPay
          newBalance = balance - paidAmount
          newAccs = updateMoneyInAccount accId tok newBalance (State.accounts state)
          warning = if ⌊ paidAmount <? amountToPay ⌋
                      then ReducePartialPay accId payee tok paidAmount amountToPay
                      else ReduceNoWarning
          (payment , finalAccs) = giveMoney accId payee tok paidAmount newAccs
          newState = record state {accounts = finalAccs}
        in
          Reduced warning payment newState cont
      )
reduceContractStep env state (If obs cont1 cont2) =
  let
    cont = if 𝒪⟦ obs ⟧ env state
             then cont1
             else cont2
  in
    Reduced ReduceNoWarning ReduceNoPayment state cont
reduceContractStep env state (When _ (mkTimeout (mkPosixTime timeout)) cont) =
  let
    interval = Environment.timeInterval env
  in
    if ⌊ PosixTime.getPosixTime (proj₁ interval) <? timeout ⌋
      then NotReduced
      else if ⌊ timeout ≤? PosixTime.getPosixTime (proj₁ interval) ⌋
             then Reduced ReduceNoWarning ReduceNoPayment state cont
             else AmbiguousTimeIntervalReductionError
reduceContractStep env state (Let valId val cont) =
  let
    evaluatedValue = ℰ⟦ val ⟧ env state
    boundVals = State.boundValues state
    newState = record state {boundValues = (valId , evaluatedValue) ↑ boundVals}
    warn = if ⌊ valId ∈ᵛ? boundVals ⌋
             then ReduceShadowing valId (valId ‼ᵛ boundVals default 0ℤ) evaluatedValue
             else ReduceNoWarning
  in
    Reduced warn ReduceNoPayment newState cont
reduceContractStep env state (Assert obs cont) =
  let
    warn = if 𝒪⟦ obs ⟧ env state
             then ReduceNoWarning
             else ReduceAssertionFailed
  in
    Reduced warn ReduceNoPayment state cont


{-# TERMINATING #-}
reduceContractUntilQuiescent : Environment → State → Contract → ReduceResult
reduceContractUntilQuiescent env state contract =
  reductionLoop false [] [] env state contract
    where
      newPayments : List Payment → ReduceEffect → List Payment
      newPayments payments ReduceNoPayment = payments
      newPayments payments (ReduceWithPayment payment) = payment ∷ payments
      newWarnings : List ReduceWarning → ReduceWarning → List ReduceWarning
      newWarnings warnings ReduceNoWarning = warnings
      newWarnings warnings warning = warning ∷ warnings
      reductionLoop : Bool → List ReduceWarning → List Payment → Environment → State → Contract → ReduceResult
      reductionLoop reduced warnings payments env state contract
        with reduceContractStep env state contract
      ... | Reduced warning effect newState cont = reductionLoop true (newWarnings warnings warning) (newPayments payments effect) env newState cont
      ... | AmbiguousTimeIntervalReductionError = RRAmbiguousTimeIntervalError
      ... | NotReduced = ContractQuiescent reduced (reverse warnings) (reverse payments) state contract


data ApplyWarning : Set where
  ApplyNoWarning : ApplyWarning
  ApplyNonPositiveDeposit : Party → AccountId → Token → Int → ApplyWarning

data ApplyAction : Set where
  AppliedAction : ApplyWarning → State → ApplyAction
  NotAppliedAction : ApplyAction


applyAction : Environment → State → InputContent → Action → ApplyAction
applyAction env state (IDeposit accId1 party1 tok1 amount) (Deposit accId2 party2 tok2 val) =
  if accId1 eqAccountId accId2 ∧ party1 eqParty party2 ∧ (tok1 eqToken tok2) ∧ ⌊ (amount ≟ ℰ⟦ val ⟧ env state) ⌋ -- TODO: Use ×-dec
    then AppliedAction
           (
             if ⌊ 0ℤ <? amount ⌋
               then ApplyNoWarning
               else ApplyNonPositiveDeposit party2 accId2 tok2 amount
           )
           (
             record state {
               accounts = addMoneyToAccount accId1 tok1 amount (State.accounts state)
             }
           )
    else NotAppliedAction
applyAction _ state (IChoice choId1 choice) (Choice choId2 bounds) =
  if ⌊ choId1 eqChoiceId choId2 ⌋ ∧ choice inBounds bounds
    then AppliedAction ApplyNoWarning (record state {choices = (choId1 , unChosenNum choice) ↑ (State.choices state)})
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
      convertReduceWarning ReduceNoWarning acc = acc
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
... | ApplyAllNoMatchError = mkError TEApplyNoMatchError
... | ApplyAllAmbiguousTimeIntervalError = mkError TEAmbiguousTimeIntervalError
... | ApplyAllHashMismatch = mkError TEHashMismatch
... | ApplyAllSuccess reduced warnings payments newState cont =
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

record Configuration : Set where
  field contract : Contract
        state : State
        environment : Environment
        warnings : List ReduceWarning
        payments : List Payment

data _⇀_ : Configuration → Configuration → Set where

  CloseRefund :
    ∀ { ϵ : Environment }
      { ω : List ReduceWarning }
      { μ : List Payment }
      { c : AssocList ChoiceId Int }
      { b : AssocList ValueId Int }
      { m : PosixTime }
      { αₓ : AccountId }
      { τ : Token }
      { ι : Int }
      { α : Accounts }
    ---------------------------------
    → record {
        contract = Close ;
        state = record {
          accounts = ( (αₓ , τ ) , ι ) ∷ α ;
          choices = c ;
          boundValues = b ;
          minTime = m
          } ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = Close ;
        state = record {
          accounts = α ;
          choices = c ;
          boundValues = b ;
          minTime = m
          } ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceNoWarning ] ;
        payments = μ ++ [ mkPayment αₓ (mkAccount αₓ) τ ι ]
      }

  PayNonPositive :
    ∀ { σ : State }
      { ϵ : Environment }
      { ν : Value }
      { αₓ : AccountId }
      { δ : Payee }
      { τ : Token }
      { γ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → ℰ⟦ ν ⟧ ϵ σ ≤ 0ℤ
    ---------------------
    → record {
        contract = Pay αₓ δ τ ν γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceNonPositivePay αₓ δ τ (ℰ⟦ ν ⟧ ϵ σ) ] ;
        payments = μ
      }

  PayInternalTransfer :
    ∀ { σ : State }
      { ϵ : Environment }
      { ν : Value }
      { αₛ αₜ : AccountId }
      { τ : Token }
      { γ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → ℰ⟦ ν ⟧ ϵ σ > 0ℤ
    ---------------------
    → let value = ℰ⟦ ν ⟧ ϵ σ
          available = moneyInAccount αₛ τ (State.accounts σ)
          paid = available ⊓ value
      in
      record {
        contract = Pay αₛ (mkAccount αₜ) τ ν γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = record σ { accounts = updateMoneyInAccount αₛ τ (available - paid) (addMoneyToAccount αₜ τ paid (State.accounts σ)) } ;
        environment = ϵ ;
        warnings = ω ++ [ if ⌊ paid <? value ⌋ then ReducePartialPay αₛ (mkAccount αₜ) τ paid value else ReduceNoWarning ];
        payments = μ
      }

  PayExternal :
    ∀ { σ : State }
      { ϵ : Environment }
      { ν : Value }
      { αₓ : AccountId }
      { τ : Token }
      { γ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
      { ξ : Party }
    → ℰ⟦ ν ⟧ ϵ σ > 0ℤ
    ---------------------
    → let value = ℰ⟦ ν ⟧ ϵ σ
          available = moneyInAccount αₓ τ (State.accounts σ)
          paid = available ⊓ value
      in
      record {
        contract = Pay αₓ (mkParty ξ) τ ν γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = record σ {accounts = updateMoneyInAccount αₓ τ (available - paid) (State.accounts σ)} ;
        environment = ϵ ;
        warnings = ω ++ [ if ⌊ paid <? value ⌋ then ReducePartialPay αₓ (mkParty ξ) τ paid value else ReduceNoWarning ] ;
        payments = μ ++ [ mkPayment αₓ (mkParty ξ) τ paid ]
      }

  IfTrue :
    ∀ { σ : State }
      { ϵ : Environment }
      { ο : Observation }
      { γ₁ γ₂ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → 𝒪⟦ ο ⟧ ϵ σ ≡ true
    ----------------------
    → record {
        contract = If ο γ₁ γ₂ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ₁ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceNoWarning ] ;
        payments = μ
      }

  IfFalse :
    ∀ { σ : State }
      { ϵ : Environment }
      { ο : Observation }
      { γ₁ γ₂ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → 𝒪⟦ ο ⟧ ϵ σ ≡ false
    -----------------------
    → record {
        contract = If ο γ₁ γ₂ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ₂ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceNoWarning ] ;
        payments = μ
      }

  WhenTimeout :
    ∀ { σ : State }
      { ϵ : Environment }
      { ο : Observation }
      { γ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
      { θ : Int }
      { ψ : List Case }
    → let (mkPosixTime startTime) = proj₁ (Environment.timeInterval ϵ) in startTime ≥ θ
    → let (mkPosixTime endTime) = proj₂ (Environment.timeInterval ϵ) in endTime ≥ θ
    --------------------------------------------------------------------------------------
    → record {
        contract = When ψ (mkTimeout (mkPosixTime θ)) γ ;
        state = σ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceNoWarning ] ;
        payments = μ
      }

  LetShadow :
    ∀ { σ : State }
      { ϵ : Environment }
      { ο : Observation }
      { γ : Contract }
      { νₓ : ValueId }
      { ν : Value }
      { ι : Int }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → νₓ ‼ᵛ State.boundValues σ ≡ just ι
    ------------------------------------------
    → record {
        contract = Let νₓ ν γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceShadowing νₓ ι (ℰ⟦ ν ⟧ ϵ σ) ] ;
        payments = μ
      }

  LetNoShadow :
    ∀ { σ : State }
      { ϵ : Environment }
      { ο : Observation }
      { γ : Contract }
      { νₓ : ValueId }
      { ν : Value }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → νₓ ‼ᵛ State.boundValues σ ≡ nothing
    -------------------------------------------    
    → record {
        contract = Let νₓ ν γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = record σ {boundValues = (νₓ , ℰ⟦ ν ⟧ ϵ σ) ↑ State.boundValues σ } ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceNoWarning ] ;
        payments = μ
      }

  AssertTrue :
    ∀ { σ : State }
      { ϵ : Environment }
      { ο : Observation }
      { γ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → 𝒪⟦ ο ⟧ ϵ σ ≡ true
    ----------------------
    → record {
        contract = Assert ο γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceNoWarning ] ;
        payments = μ
      }

  AssertFalse :
    ∀ { σ : State }
      { ϵ : Environment }
      { ο : Observation }
      { γ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
    → 𝒪⟦ ο ⟧ ϵ σ ≡ false
    -----------------------
    → record {
        contract = Assert ο γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω;
        payments = μ
      }
      ⇀
      record {
        contract = γ ;
        state = σ ;
        environment = ϵ ;
        warnings = ω ++ [ ReduceAssertionFailed ] ;
        payments = μ
      }


-- reflexive and transitive closure

infix  2 _⇀⋆_
infix  1 begin_
infixr 2 _⇀⟨_⟩_
infix  3 _∎

data _⇀⋆_ : Configuration → Configuration → Set where
  _∎ : ∀ M
      ------
    → M ⇀⋆ M

  _⇀⟨_⟩_ : ∀ L {M N}
    → L ⇀ M
    → M ⇀⋆ N
      ------
    → L ⇀⋆ N

begin_ : ∀ {M N}
  → M ⇀⋆ N
    ------
  → M ⇀⋆ N
begin M⇀⋆N = M⇀⋆N

{-
data Quiescent : Configuration → Set where

  close :
    ∀ { ϵ : Environment }
      { ω : List ReduceWarning }
      { μ : List Payment }
    ---------------------
    → Quiescent record {
          contract = Close ;
          state =
            record
              { accounts = [] ;
                choices = emptyMap _eqChoiceId_ ;
                boundValues = emptyMap _eqValueId_ ;
                minTime =  mkPosixTime 0ℤ } ;
            environment = ϵ ;
            warnings = ω;
            payments = μ
        }

  waiting :
    ∀ { ϵ : Environment }
      { case : Case }
      { cases : List Case }
      { τ : Timeout }
      { γ : Contract }
      { ω : List ReduceWarning }
      { μ : List Payment }
    ---------------------
    → Quiescent record {
          contract = When (case ∷ cases) τ γ ;
          state =
            record
              { accounts = [] ;
                choices = emptyMap _eqChoiceId_ ;
                boundValues = emptyMap _eqValueId_ ;
                minTime =  mkPosixTime 0ℤ } ;
            environment = ϵ ;
            warnings = ω;
            payments = μ
        }

-- Quiescent contracts do not reduce
Quiescent¬⇀ : ∀ {C₁ C₂}
  → Quiescent C₁
  ---------------
  → ¬ (C₁ ⇀⋆ C₂)
Quiescent¬⇀ close x = {!!}
Quiescent¬⇀ waiting = {!!}
-}
