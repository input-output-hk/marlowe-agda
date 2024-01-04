---
title: Marlowe.Semantics.Evaluate
layout: page
---

```
module Marlowe.Semantics.Evaluate where
```

## Imports

```
open import Data.Bool using (Bool; false; true; _∧_; _∨_; if_then_else_; not)
open import Data.Integer using (ℤ; -_; _-_; +_; _+_; _*_; _≟_; _<?_; _≤?_; ∣_∣; 0ℤ; 1ℤ; NonZero)
open import Data.Integer.DivMod using (_div_)
open import Data.Nat as ℕ using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; fromWitnessFalse)

open import Contrib.Data.List.AssocList
open import Marlowe.Language.Contract
open import Marlowe.Language.State

open Environment using (timeInterval)
open TimeInterval using (startTime; offset)
open PosixTime using (getPosixTime)
open State using (accounts; boundValues; choices)

open Decidable _≟-AccountId×Token_ renaming (_‼_default_ to _‼ᵃ_default_) using ()
open Decidable _≟-ChoiceId_ renaming (_‼_default_ to _‼ᶜ_default_) using (_∈?_)
open Decidable _≟-ValueId_ renaming (_‼_default_ to _‼ᵛ_default_) using ()
```

## Evaluation of `Value`s and `Observation`s

```
ℰ⟦_⟧ : Value → Environment → State → ℤ
𝒪⟦_⟧ : Observation → Environment → State → Bool
```

### Value

```
ℰ⟦ AvailableMoney a t ⟧ _ s = + ((a , t) ‼ᵃ accounts s default 0)
ℰ⟦ Constant x ⟧ _ _ = x
ℰ⟦ NegValue x ⟧ e s = - ℰ⟦ x ⟧ e s
ℰ⟦ AddValue x y ⟧ e s = ℰ⟦ x ⟧ e s + ℰ⟦ y ⟧ e s
ℰ⟦ SubValue x y ⟧ e s = ℰ⟦ x ⟧ e s - ℰ⟦ y ⟧ e s
ℰ⟦ MulValue x y ⟧ e s = ℰ⟦ x ⟧ e s * ℰ⟦ y ⟧ e s
ℰ⟦ DivValue x y ⟧ e s = ℰ⟦ x ⟧ e s / ℰ⟦ y ⟧ e s
  where
    _/_ : ℤ → ℤ → ℤ
    _/_ num den with ∣ den ∣ ℕ.≟ 0
    ... | yes _ = 0ℤ
    ... | no ¬p = (num div den) { fromWitnessFalse ¬p }
ℰ⟦ ChoiceValue c ⟧ _ s = c ‼ᶜ choices s default 0ℤ
ℰ⟦ TimeIntervalStart ⟧ e _ = + getPosixTime (startTime (timeInterval e))
ℰ⟦ TimeIntervalEnd ⟧ e _ = + getPosixTime (endTime (timeInterval e))
ℰ⟦ UseValue v ⟧ _ s = v ‼ᵛ boundValues s default 0ℤ
ℰ⟦ Cond o x y ⟧ e s = if 𝒪⟦ o ⟧ e s then ℰ⟦ x ⟧ e s else ℰ⟦ y ⟧ e s
```

### Observation

```
𝒪⟦ AndObs x y ⟧ e s = 𝒪⟦ x ⟧ e s ∧ 𝒪⟦ y ⟧ e s
𝒪⟦ OrObs x y ⟧ e s = 𝒪⟦ x ⟧ e s ∨ 𝒪⟦ y ⟧ e s
𝒪⟦ NotObs x ⟧ e s = not (𝒪⟦ x ⟧ e s)
𝒪⟦ ChoseSomething c ⟧  _ s = ⌊ c ∈? choices s ⌋
𝒪⟦ ValueGE y x ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≤? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueGT y x ⟧ e s = ⌊ ℰ⟦ x ⟧ e s <? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueLT x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s <? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueLE x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≤? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueEQ x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≟ ℰ⟦ y ⟧ e s ⌋
𝒪⟦ TrueObs ⟧ _ _ = true
𝒪⟦ FalseObs ⟧ _ _ = false
```
