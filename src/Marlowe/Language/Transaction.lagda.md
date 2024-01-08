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

## Parameterized domain

The domain model used for building the transaction related
data types is parameterized by `Party` and `Token`.

```
module Parameterized
  {Party : Set}
  {Token : Set}
  where

  open import Marlowe.Language.Contract as Contract
  open import Marlowe.Language.Input as Input
  open import Marlowe.Language.State as State

  open Contract.Parameterized {Party} {Token}
  open Input.Parameterized {Party} {Token}
  open State.Parameterized {Party} {Token}
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
