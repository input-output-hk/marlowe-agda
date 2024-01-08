---
title: Marlowe.Language.Contract
layout: page
---

This module specifies the domain model for a Marlowe contract.

```
module Marlowe.Language.Contract where
```

## Imports

```
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
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

### Bound

`Choice`s are bound. The `Bound` data type is a tuple of
integers that represents an inclusive lower and upper bound.

```
data Bound : Set where
  mkBound : ℤ → ℤ → Bound
```

## Parameterized domain

The domain model used for building the `Contract` data type is
parameterized by `Party` and `Token`.

```
module Parameterized
  {Party : Set}
  {Token : Set}
  where
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

### Payee

A contract can transfer assets between accounts or from an account to a party.
This is modelled in `Payee`.

```
  data Payee : Set where
    mkAccount : AccountId → Payee
    mkParty : Party → Payee
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

## Export to Haskell

```
{-

{-# FOREIGN GHC import Marlowe.Core.Contract #-}
{-# COMPILE GHC PosixTime = data PosixTime (PosixTime) #-}
{-# COMPILE GHC Timeout = data Timeout (Timeout) #-}
{-# COMPILE GHC Parameterized.AccountId = data AccountId (AccountId) #-}
{-# COMPILE GHC ChoiceName = data ChoiceName (ChoiceName)  #-}
{-# COMPILE GHC Parameterized.ChoiceId = data ChoiceId (ChoiceId) #-}
{-# COMPILE GHC ValueId = data ValueId (ValueId) #-}
{-# COMPILE GHC Parameterized.Payee = data Payee (Account | Party) #-}
{-# COMPILE GHC Parameterized.Observation = data Observation (AndObs | OrObs | NotObs | ChoseSomething | ValueGE | ValueGT | ValueLT | ValueLE | ValueEQ | TrueObs | FalseObs) #-}
{-# COMPILE GHC Parameterized.Value = data Value (AvailableMoney | Constant | NegValue | AddValue | SubValue | MulValue | DivValue | ChoiceValue | TimeIntervalStart | TimeIntervalEnd | UseValue | Cond) #-}
{-# COMPILE GHC Bound = data Bound (Bound) #-}
{-# COMPILE GHC Parameterized.Action = data Action (Deposit | Choice | Notify) #-}
{-# COMPILE GHC Parameterized.Case = data Case (Case) #-}
{-# COMPILE GHC Parameterized.Contract = data Contract (Close | Pay | If | When | Let | Assert) #-}

-}
```
