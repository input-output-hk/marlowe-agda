
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

open State using (accounts; boundValues; choices)

record Configuration : Set where
  field contract : Contract
        state : State
        environment : Environment
        warnings : List ReduceWarning
        payments : List Payment

data _⇀_ : Configuration → Configuration → Set where

  CloseRefund :
    ∀ { e : Environment }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { as : AssocList (AccountId × Token) Int }
      { cs : AssocList ChoiceId Int }
      { vs : AssocList ValueId Int }
      { m : PosixTime }
      { a : AccountId }
      { t : Token }
      { i : Int }
    --------------------------------------------
    → record {
        contract = Close ;
        state = record {
          accounts = ( (a , t ) , i ) ∷ as ;
          choices = cs ;
          boundValues = vs ;
          minTime = m
          } ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = Close ;
        state = record {
          accounts = as ;
          choices = cs ;
          boundValues = vs ;
          minTime = m
          } ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps ++ [ mkPayment a (mkAccount a) t i ]
      }

  PayNonPositive :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { a : AccountId }
      { y : Payee }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → ℰ⟦ v ⟧ e s ≤ 0ℤ
    ---------------------
    → record {
        contract = Pay a y t v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNonPositivePay a y t (ℰ⟦ v ⟧ e s) ] ;
        payments = ps
      }

  PayInternalTransfer :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { aₛ aₜ : AccountId }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → ℰ⟦ v ⟧ e s > 0ℤ
    ---------------------
    → let value = ℰ⟦ v ⟧ e s
          available = moneyInAccount aₛ t (accounts s)
          paid = available ⊓ value
      in
      record {
        contract = Pay aₛ (mkAccount aₜ) t v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s { accounts = updateMoneyInAccount aₛ t (available - paid) (addMoneyToAccount aₜ t paid (accounts s)) } ;
        environment = e ;
        warnings = ws ++ [ if ⌊ paid <? value ⌋ then ReducePartialPay aₛ (mkAccount aₜ) t paid value else ReduceNoWarning ];
        payments = ps
      }

  PayExternal :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { aₓ : AccountId }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { p : Party }
    → ℰ⟦ v ⟧ e s > 0ℤ
    ---------------------
    → let value = ℰ⟦ v ⟧ e s
          available = moneyInAccount aₓ t (accounts s)
          paid = available ⊓ value
      in
      record {
        contract = Pay aₓ (mkParty p) t v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s {accounts = updateMoneyInAccount aₓ t (available - paid) (accounts s)} ;
        environment = e ;
        warnings = ws ++ [ if ⌊ paid <? value ⌋ then ReducePartialPay aₓ (mkParty p) t paid value else ReduceNoWarning ] ;
        payments = ps ++ [ mkPayment aₓ (mkParty p) t paid ]
      }

  IfTrue :
    ∀ { s : State }
      { e : Environment }
      { ο : Observation }
      { c₁ c₂ : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ ο ⟧ e s ≡ true
    ----------------------
    → record {
        contract = If ο c₁ c₂ ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c₁ ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  IfFalse :
    ∀ { s : State }
      { e : Environment }
      { ο : Observation }
      { c₁ c₂ : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ ο ⟧ e s ≡ false
    -----------------------
    → record {
        contract = If ο c₁ c₂ ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c₂ ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  WhenTimeout :
    ∀ { s : State }
      { e : Environment }
      { ο : Observation }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { t : Int }
      { cs : List Case }
    → let (mkPosixTime startTime) = proj₁ (Environment.timeInterval e) in startTime ≥ t
    → let (mkPosixTime endTime) = proj₂ (Environment.timeInterval e) in endTime ≥ t
    --------------------------------------------------------------------------------------
    → record {
        contract = When cs (mkTimeout (mkPosixTime t)) c ;
        state = s;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  LetShadow :
    ∀ { s : State }
      { e : Environment }
      { ο : Observation }
      { c : Contract }
      { vₓ : ValueId }
      { v : Value }
      { ι : Int }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → vₓ ‼ᵛ boundValues s ≡ just ι
    ------------------------------------------
    → record {
        contract = Let vₓ v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceShadowing vₓ ι (ℰ⟦ v ⟧ e s) ] ;
        payments = ps
      }

  LetNoShadow :
    ∀ { s : State }
      { e : Environment }
      { ο : Observation }
      { c : Contract }
      { vₓ : ValueId }
      { v : Value }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → vₓ ‼ᵛ boundValues s ≡ nothing
    -------------------------------------------    
    → record {
        contract = Let vₓ v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s {boundValues = (vₓ , ℰ⟦ v ⟧ e s) ↑ boundValues s } ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  AssertTrue :
    ∀ { s : State }
      { e : Environment }
      { ο : Observation }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ ο ⟧ e s ≡ true
    ----------------------
    → record {
        contract = Assert ο c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  AssertFalse :
    ∀ { s : State }
      { e : Environment }
      { ο : Observation }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ ο ⟧ e s ≡ false
    -----------------------
    → record {
        contract = Assert ο c ;
        state = s ;
        environment = e ;
        warnings = ws;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceAssertionFailed ] ;
        payments = ps
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
    ∀ { e : Environment }
      { ws : List ReduceWarning }
      { ps : List Payment }
    ---------------------
    → Quiescent record {
          contract = Close ;
          state =
            record
              { accounts = [] ;
                choices = emptyMap _eqChoiceId_ ;
                boundValues = emptyMap _eqValueId_ ;
                minTime =  mkPosixTime 0ℤ } ;
            environment = e ;
            warnings = ws;
            payments = ps
        }

  waiting :
    ∀ { e : Environment }
      { case : Case }
      { cases : List Case }
      { t : Timeout }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    ---------------------
    → Quiescent record {
          contract = When (case ∷ cases) t c ;
          state =
            record
              { accounts = [] ;
                choices = emptyMap _eqChoiceId_ ;
                boundValues = emptyMap _eqValueId_ ;
                minTime =  mkPosixTime 0ℤ } ;
            environment = e ;
            warnings = ws;
            payments = ps
        }

-- Quiescent contracts do not reduce
Quiescent¬⇀ : ∀ {C₁ C₂}
  → Quiescent C₁
  ---------------
  → ¬ (C₁ ⇀⋆ C₂)
Quiescent¬⇀ close x = {!!}
Quiescent¬⇀ waiting = {!!}
-}
