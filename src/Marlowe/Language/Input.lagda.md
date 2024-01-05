---
title: Marlowe.Language.Input
layout: page
---

```
module Marlowe.Language.Input where

open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Data.Bool using (Bool; _∧_)
open import Data.Integer using (_≤?_)
open import Data.Nat using (ℕ)
open import Data.List using (any)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (⌊_⌋)

data ChosenNum : Set where
  mkChosenNum : Int → ChosenNum

unChosenNum : ChosenNum → Int
unChosenNum (mkChosenNum num) = num

module Domain
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)

  where

  import Marlowe.Language.Contract as Contract
  open Contract.Domain _≟-Party_ _≟-Token_

  _inBounds_ : ChosenNum → List Bound → Bool
  _inBounds_ (mkChosenNum num) bounds =
    any inBound bounds
      where
        inBound : Bound → Bool
        inBound (Bound.mkBound l u) = ⌊ l ≤? num ⌋ ∧ ⌊ num ≤? u ⌋

  data InputContent : Set where
    IDeposit : AccountId → Party → Token → ℕ → InputContent
    IChoice : ChoiceId → ChosenNum → InputContent
    INotify : InputContent

  data Input : Set where
    NormalInput : InputContent → Input

  getInputContent : Input → InputContent
  getInputContent (NormalInput input) = input where open Input
```
