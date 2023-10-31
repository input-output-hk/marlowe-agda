
module Marlowe.Language.Transaction where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Data.Nat using (ℕ)
open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Primitives


data IntervalError : Set where
  InvalidInterval : TimeInterval → IntervalError
  IntervalInPastError : PosixTime → TimeInterval → IntervalError
  

data IntervalResult : Set where
  IntervalTrimmed : Environment → State → IntervalResult
  mkIntervalError : IntervalError → IntervalResult


data Payment : Set where
  mkPayment : AccountId → Payee → Token → ℕ → Payment
  

data TransactionWarning : Set where
  TransactionNonPositiveDeposit : Party → AccountId → Token → Int → TransactionWarning
  TransactionNonPositivePay : AccountId → Payee → Token → Int → TransactionWarning
  TransactionPartialPay : AccountId → Payee → Token → Int → Int → TransactionWarning
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
