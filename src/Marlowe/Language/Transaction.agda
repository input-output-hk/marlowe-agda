module Marlowe.Language.Transaction where

open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Contrib.Data.List.AssocList
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Function.Base using (_∘_)

open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State

data IntervalError : Set where
  InvalidInterval : TimeInterval → IntervalError
  IntervalInPastError : PosixTime → TimeInterval → IntervalError

data IntervalResult : Set where
  IntervalTrimmed : Environment → State → IntervalResult
  mkIntervalError : IntervalError → IntervalResult

record Payment : Set where
  constructor mkPayment
  field
    accountId : AccountId
    payee : Payee
    token : Token
    amount : ℕ

data TransactionWarning : Set where
  TransactionNonPositiveDeposit : Party → AccountId → Token → Int → TransactionWarning
  TransactionNonPositivePay : AccountId → Payee → Token → Int → TransactionWarning
  TransactionPartialPay : AccountId → Payee → Token → ℕ → ℕ → TransactionWarning
  TransactionShadowing : ValueId → Int → Int → TransactionWarning
  TransactionAssertionFailed : TransactionWarning

data TransactionError : Set where
  TEAmbiguousTimeIntervalError : TransactionError
  TEApplyNoMatchError : TransactionError
  TEIntervalError : IntervalError → TransactionError
  TEUselessTransaction : TransactionError
  TEHashMismatch : TransactionError

data TransactionInput : Set where
  mkTransactionInput : TimeInterval → List Input → TransactionInput


data TransactionOutput : Set where
  mkTransactionOutput : List TransactionWarning → List Payment → State → Contract → TransactionOutput
  mkError : TransactionError → TransactionOutput

Σ-payments : List Payment → AssocList Token ℕ
Σ-payments = map λ {(mkPayment _ _ t n) → (t , n)}

filter-payments : Token → List Payment → List Payment
filter-payments t = filter (λ {(mkPayment _ _ t′ _) → (t ≟-Token t′)})
