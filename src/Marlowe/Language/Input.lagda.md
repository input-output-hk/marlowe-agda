---
title: Marlowe.Language.Input
layout: page
---

```
module Marlowe.Language.Input where
```

## Imports

```
open import Data.Bool using (Bool; _∧_)
open import Data.Integer using (ℤ; _≤?_)
open import Data.Nat using (ℕ)
open import Data.List using (List; any)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (⌊_⌋)
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

```
module Parameterized
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where

  open import Marlowe.Language.Contract as Contract
  open Contract.Parameterized _≟-Party_ _≟-Token_
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
