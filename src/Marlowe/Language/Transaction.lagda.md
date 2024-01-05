---
title: Marlowe.Language.Transaction
layout: page
---

```
module Marlowe.Language.Transaction where
```

## Imports

```
open import Contrib.Data.List.AssocList
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (DecidableEquality)
open import Function.Base using (_∘_)
```

```
module Domain
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)

  where

  open import Marlowe.Language.Contract as Contract
  open import Marlowe.Language.Input as Input
  open import Marlowe.Language.State as State

  open Contract.Domain _≟-Party_ _≟-Token_
  open Input.Domain _≟-Party_ _≟-Token_
  open State.Domain _≟-Party_ _≟-Token_
```

## Payment

```
  record Payment : Set where
    constructor _[_,_]↦_
    field
      accountId : AccountId
      token : Token
      amount : ℕ
      payee : Payee
```

### Interval result

```
  data IntervalError : Set where
    InvalidInterval : TimeInterval → IntervalError
    IntervalInPastError : PosixTime → TimeInterval → IntervalError

  data IntervalResult : Set where
    IntervalTrimmed : Environment → State → IntervalResult
    mkIntervalError : IntervalError → IntervalResult
```

### Transaction warnings and errors

```
  data TransactionWarning : Set where
    TransactionNonPositiveDeposit : Party → AccountId → Token → ℤ → TransactionWarning
    TransactionNonPositivePay : AccountId → Payee → Token → ℤ → TransactionWarning
    TransactionPartialPay : AccountId → Payee → Token → ℕ → ℕ → TransactionWarning
    TransactionShadowing : ValueId → ℤ → ℤ → TransactionWarning
    TransactionAssertionFailed : TransactionWarning

  data TransactionError : Set where
    TEAmbiguousTimeIntervalError : TransactionError
    TEApplyNoMatchError : TransactionError
    TEIntervalError : IntervalError → TransactionError
    TEUselessTransaction : TransactionError
    TEHashMismatch : TransactionError
```

## TransactionInput

We use transactions to move contracts forward. Transactions are comprised
of a list of inputs (possibly empty) to be applied within a TimeInterval

```
  record TransactionInput : Set where
    constructor mkTransactionInput
    field
      timeInterval : TimeInterval
      inputs : List Input
```

## TransactionOutput

```
  data TransactionOutput : Set where
    mkTransactionOutput : List TransactionWarning → List Payment → State → Contract → TransactionOutput
    mkError : TransactionError → TransactionOutput
```
