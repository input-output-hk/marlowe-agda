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
  constructor _[_,_]↦_
  field
    accountId : AccountId
    token : Token
    amount : ℕ
    payee : Payee

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

record TransactionInput : Set where
  constructor mkTransactionInput
  field
    timeInterval : TimeInterval
    inputs : List Input

data TransactionOutput : Set where
  mkTransactionOutput : List TransactionWarning → List Payment → State → Contract → TransactionOutput
  mkError : TransactionError → TransactionOutput

projₚ : Token → Payment → ℕ
projₚ t (a [ t′ , n ]↦ _) = 1ₜ t (t′ , n)

Σ-payments : Token → List Payment → ℕ
Σ-payments t = sum ∘ map (projₚ t)

filter-payments : Token → List Payment → List Payment
filter-payments t = filter (λ {(_ [ t′ , _ ]↦ _) → (t ≟-Token t′)})
