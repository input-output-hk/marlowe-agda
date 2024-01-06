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
open import Data.Bool using (Bool; false; _∧_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Nat as ℕ using (ℕ; _⊔_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Function.Base using (_∘_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; _≡_; _≢_)
open import Relation.Nullary using (yes; no)
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

## Parameterized domain

The domain model used for building the `Contract` data type is
parameterized by `Party` and `Token`.

```
module Parameterized
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where
```

### AccountId

Local accounts for parties of a contract are identified by the
`AccountId`. In order to allow lookups by `AccountId` we need
to provide an instance of `DecidableEquality` as well.

```
  data AccountId : Set where
    mkAccountId : Party → AccountId

  unAccountId : AccountId → Party
  unAccountId (mkAccountId p) = p

  _≟-AccountId_ : DecidableEquality AccountId
  mkAccountId p₁ ≟-AccountId mkAccountId p₂ with p₁ ≟-Party p₂
  ... | yes p = yes (cong mkAccountId p)
  ... | no ¬p = no (¬p ∘ cong unAccountId)
```

### ChoiceId

Choices are identified by a `ChoiceId` which is defined by a 
canonical name and the `Party` that has to make the choice.

```
  data ChoiceName : Set where
    mkChoiceName : String → ChoiceName

  _≟-ChoiceName_ : DecidableEquality ChoiceName
  mkChoiceName s₁ ≟-ChoiceName mkChoiceName s₂ with s₁ ≟ s₂
  ... | yes p = yes (cong mkChoiceName p)
  ... | no ¬p = no (¬p ∘ cong λ {(mkChoiceName s) → s})

  record ChoiceId : Set where
    constructor mkChoiceId
    field
      name : ChoiceName
      party : Party

  open ChoiceId

  _≟-ChoiceId_ : DecidableEquality ChoiceId
  mkChoiceId n₁ p₁ ≟-ChoiceId mkChoiceId n₂ p₂ with n₁ ≟-ChoiceName n₂ | p₁ ≟-Party p₂
  ... | yes p | yes q = yes (cong₂ mkChoiceId p q)
  ... | _ | no ¬q = no (¬q ∘ cong party)
  ... | no ¬p | _ = no (¬p ∘ cong name)
```

### ValueId

The `ValueId` is used to store and reference `Value`s in the state of the
contract.

```
  data ValueId : Set where
    mkValueId : String → ValueId

  _≟-ValueId_ : DecidableEquality ValueId
  mkValueId s₁ ≟-ValueId mkValueId s₂ with s₁ ≟ s₂
  ... | yes p = yes (cong mkValueId p)
  ... | no ¬p = no (¬p ∘ cong λ {(mkValueId s) → s})
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

## Bound

`Choice`s are bound. The `Bound` data type is a tuple of
integers that represents an inclusive lower and upper bound.

```
  data Bound : Set where
    mkBound : ℤ → ℤ → Bound
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
