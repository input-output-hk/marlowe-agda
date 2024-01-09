---
title: Marlowe.Language
layout: page
---

This module specifies the domain model for a Marlowe contract.

```
module Marlowe.Language where
```

## Imports

```
open import Contrib.Data.List.AssocList
open import Data.Bool using (Bool; _∧_)
open import Data.Integer using (ℤ; _≤?_)
open import Data.List using (List; []; _∷_; any)
open import Data.Nat using (ℕ; _⊔_; _+_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Function.Base using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
```

## PosixTime and Timeout

Timeouts for applying inputs are represented as PosixTime.

```
record PosixTime : Set where
  constructor mkPosixTime
  field
    getPosixTime : ℕ

data Timeout : Set where
  mkTimeout : PosixTime → Timeout
```

## TimeInterval

```
record TimeInterval : Set where
  constructor mkInterval
  field
    startTime : PosixTime
    offset : ℕ

endTime : TimeInterval → PosixTime
endTime (mkInterval (mkPosixTime s) o) = mkPosixTime (s + o)
```

## Environment

```
record Environment : Set where
  constructor mkEnvironment
  field
    timeInterval : TimeInterval

interval-end : Environment → ℕ
interval-end (mkEnvironment (mkInterval (mkPosixTime s) o)) = s + o
```

### ValueId

The `ValueId` is used to store and reference `Value`s in the state of the
contract.

```
data ValueId : Set where
  mkValueId : String → ValueId
```

### ChoiceName

```
data ChoiceName : Set where
  mkChoiceName : String → ChoiceName
```

### ChosenNum

In order to interpret integers in the context of `Choice`s, we make use
of the type `ChosenNum`.
```
data ChosenNum : Set where
  mkChosenNum : ℤ → ChosenNum

unChosenNum : ChosenNum → ℤ
unChosenNum (mkChosenNum num) = num
```

### Bound

`Choice`s are bound. The `Bound` data type is a tuple of
integers that represents an inclusive lower and upper bound.

```
data Bound : Set where
  mkBound : ℤ → ℤ → Bound
```

In order to determine, if a `ChosenNum` is within the inclusive bounds list,
we use the `inBounds` function.

```
_inBounds_ : ChosenNum → List Bound → Bool
_inBounds_ (mkChosenNum num) bounds =
  any inBound bounds
    where
      inBound : Bound → Bool
      inBound (Bound.mkBound l u) = ⌊ l ≤? num ⌋ ∧ ⌊ num ≤? u ⌋
```

## Parameterized by Party

```
module PartyParam (Party : Set) where
```

### AccountId

Local accounts for parties of a contract are identified by the
`AccountId`.

```
  data AccountId : Set where
    mkAccountId : Party → AccountId

  unAccountId : AccountId → Party
  unAccountId (mkAccountId p) = p
```

### Payee

A contract can transfer assets between accounts or from an account to a party.
This is modelled in `Payee`.

```
  data Payee : Set where
    mkAccount : AccountId → Payee
    mkParty : Party → Payee
```

### ChoiceId

Choices are identified by a `ChoiceId` which is defined by a 
canonical name and the `Party` that has to make the choice.

```
  record ChoiceId : Set where
    constructor mkChoiceId
    field
      name : ChoiceName
      party : Party
```

## Parameterized by Token

```
  module TokenParam (Token : Set) where
```

## Values and observations

Values and observations are language terms that interact with most of the
other constructs. Value evaluates to an integer and observation evaluates to
a boolean respectively. They are defined mutually recursive.

```
    data Value : Set
    data Observation : Set
```

#### Value

```
    data Value where
      AvailableMoney : AccountId → Token → Value
      Constant : ℤ → Value
      NegValue : Value → Value
      AddValue : Value → Value → Value
      SubValue : Value → Value → Value
      MulValue : Value → Value → Value
      DivValue : Value → Value → Value
      ChoiceValue : ChoiceId → Value
      TimeIntervalStart : Value
      TimeIntervalEnd : Value
      UseValue : ValueId → Value
      Cond : Observation → Value → Value → Value
```

#### Observation

```
    data Observation where
      AndObs : Observation → Observation → Observation
      OrObs : Observation → Observation → Observation
      NotObs : Observation → Observation
      ChoseSomething : ChoiceId → Observation
      ValueGE : Value → Value → Observation
      ValueGT : Value → Value → Observation
      ValueLT : Value → Value → Observation
      ValueLE : Value → Value → Observation
      ValueEQ : Value → Value → Observation
      TrueObs : Observation
      FalseObs : Observation
```

## Actions

Actions are the counterparts to inputs, i.e. a given input can trigger a
certain action.

```
    data Action : Set where
      Deposit : AccountId → Party → Token → Value → Action
      Choice : ChoiceId → List Bound → Action
      Notify : Observation → Action
```

## Contract

Marlowe is a continuation-based language. A `Contract` is represented as a tree
structure with `Close` contracts in the leaves. A branch in the tree represents
a possible exection path of the contract.

`Case` and `Contract` are defined mutually recursive to allow to specify the
continuation for a given action as another contract.

```
    data Case : Set
    data Contract : Set

    data Case where
      mkCase : Action → Contract → Case

    data Contract where
      Close : Contract
      Pay : AccountId → Payee → Token → Value → Contract → Contract
      If : Observation → Contract → Contract → Contract
      When : List Case → Timeout → Contract → Contract
      Let : ValueId → Value → Contract → Contract
      Assert : Observation → Contract → Contract
```

The `When` constructor allows for applying inputs before a specified timeout.

## State

```
    record State : Set where
      constructor ⟨_,_,_,_⟩
      field
        accounts : AssocList (AccountId × Token) ℕ
        choices : AssocList ChoiceId ℤ
        boundValues : AssocList ValueId ℤ
        minTime : PosixTime

    emptyState : PosixTime → State
    emptyState m = ⟨ [] , [] , [] , m ⟩
```

### Payment

```
    record Payment : Set where
      constructor _[_,_]↦_
      field
        accountId : AccountId
        token : Token
        amount : ℕ
        payee : Payee
```

## InputContent

```
    data InputContent : Set where
      IDeposit : AccountId → Party → Token → ℕ → InputContent
      IChoice : ChoiceId → ChosenNum → InputContent
      INotify : InputContent
```

## Input

```
    data Input : Set where
      NormalInput : InputContent → Input
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

## TransactionOutput

```
    data TransactionOutput : Set where
      mkTransactionOutput : List TransactionWarning → List Payment → State → Contract → TransactionOutput
      mkError : TransactionError → TransactionOutput
```


### Expiry

All contracts are finite and have an expiration time. The expiration time is
the maximum of all timeouts in the contract.

```
    maxTimeout : Contract → ℕ
    maxTimeout Close = 0
    maxTimeout (Pay _ _ _ _ c) = maxTimeout c
    maxTimeout (If _ c₁ c₂) = maxTimeout c₁ ⊔ maxTimeout c₂
    maxTimeout (When [] (mkTimeout (mkPosixTime t)) c) = t ⊔ maxTimeout c
    maxTimeout (When ((mkCase _ cₐ) ∷ cs) t c) = maxTimeout cₐ ⊔ maxTimeout (When cs t c)
    maxTimeout (Let _ _ c) = maxTimeout c
    maxTimeout (Assert _ c) = maxTimeout c
```

## DecidableEquality

```
module Equality
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where

  open PartyParam Party
  open TokenParam Token

  _≟-AccountId_ : DecidableEquality AccountId
  mkAccountId p₁ ≟-AccountId mkAccountId p₂ with p₁ ≟-Party p₂
  ... | yes p = yes (cong mkAccountId p)
  ... | no ¬p = no (¬p ∘ cong unAccountId)

  _≟-ChoiceName_ : DecidableEquality ChoiceName
  mkChoiceName s₁ ≟-ChoiceName mkChoiceName s₂ with s₁ ≟ s₂
  ... | yes p = yes (cong mkChoiceName p)
  ... | no ¬p = no (¬p ∘ cong λ {(mkChoiceName s) → s})

  _≟-ChoiceId_ : DecidableEquality ChoiceId
  mkChoiceId n₁ p₁ ≟-ChoiceId mkChoiceId n₂ p₂ with n₁ ≟-ChoiceName n₂ | p₁ ≟-Party p₂
  ... | yes p | yes q = yes (cong₂ mkChoiceId p q)
  ... | _ | no ¬q = no (¬q ∘ cong ChoiceId.party)
  ... | no ¬p | _ = no (¬p ∘ cong ChoiceId.name)

  _≟-ValueId_ : DecidableEquality ValueId
  mkValueId s₁ ≟-ValueId mkValueId s₂ with s₁ ≟ s₂
  ... | yes p = yes (cong mkValueId p)
  ... | no ¬p = no (¬p ∘ cong λ {(mkValueId s) → s})
```

## Export to Haskell

```
open PartyParam
open TokenParam

{-# FOREIGN GHC import Marlowe.Core.Contract #-}
{-# COMPILE GHC PosixTime = data PosixTime (PosixTime) #-}
{-# COMPILE GHC Timeout = data Timeout (Timeout) #-}
{-# COMPILE GHC AccountId = data AccountId (AccountId) #-}
{-# COMPILE GHC ChoiceName = data ChoiceName (ChoiceName)  #-}
{-# COMPILE GHC ChoiceId = data ChoiceId (ChoiceId) #-}
{-# COMPILE GHC ValueId = data ValueId (ValueId) #-}
{-# COMPILE GHC Payee = data Payee (Account | Party) #-}
{-# COMPILE GHC Observation = data Observation (AndObs | OrObs | NotObs | ChoseSomething | ValueGE | ValueGT | ValueLT | ValueLE | ValueEQ | TrueObs | FalseObs) #-}
{-# COMPILE GHC Value = data Value (AvailableMoney | Constant | NegValue | AddValue | SubValue | MulValue | DivValue | ChoiceValue | TimeIntervalStart | TimeIntervalEnd | UseValue | Cond) #-}
{-# COMPILE GHC Bound = data Bound (Bound) #-}
{-# COMPILE GHC Action = data Action (Deposit | Choice | Notify) #-}
{-# COMPILE GHC Case = data Case (Case) #-}
{-# COMPILE GHC Contract = data Contract (Close | Pay | If | When | Let | Assert) #-}
```
