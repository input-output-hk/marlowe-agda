```agda
open import Marlowe.Abstract

module Marlowe.Semantics.Evaluate (ma : MarloweAbstract) (open MarloweAbstract ma)
  where
```

<!--
## Imports

```agda
open import Data.Bool using (false; true; _∧_; _∨_; if_then_else_; not) renaming (Bool to 𝔹)
open import Data.Integer as ℤ using (ℤ; -_; _-_; +_; _+_; _*_; _≟_; _<?_; _≤?_; ∣_∣; 0ℤ; 1ℤ; NonZero)
open import Data.Integer.DivMod as ℤ using ()
open import Data.Nat as ℕ using (ℕ)
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; fromWitnessFalse)

open import Marlowe.Language ma
open Environment using (timeInterval)
open State using (accounts; choices; boundValues)
open TimeInterval using (startTime; offset)
open PosixTime using (getPosixTime)

open import Class.Default
open import Class.Decidable
open import Prelude.AssocList
open import Prelude.Irrelevance
```
-->

## Evaluation of `Value`s and `Observation`s

```agda
ℰ⟦_⟧ : Value → Environment → State → ℤ
𝒪⟦_⟧ : Observation → Environment → State → 𝔹
```

### Value

```agda
ℰ⟦ AvailableMoney a t ⟧ _ s = + ((accounts s) ‼d (a , t))
ℰ⟦ Constant x ⟧ _ _ = x
ℰ⟦ NegValue x ⟧ e s = - ℰ⟦ x ⟧ e s
ℰ⟦ AddValue x y ⟧ e s = ℰ⟦ x ⟧ e s + ℰ⟦ y ⟧ e s
ℰ⟦ SubValue x y ⟧ e s = ℰ⟦ x ⟧ e s - ℰ⟦ y ⟧ e s
ℰ⟦ MulValue x y ⟧ e s = ℰ⟦ x ⟧ e s * ℰ⟦ y ⟧ e s
ℰ⟦ DivValue x y ⟧ e s = ℰ⟦ x ⟧ e s / ℰ⟦ y ⟧ e s
  where
    _/_ : ℤ → ℤ → ℤ
    _/_ num den with den ℤ.≟ 0ℤ
    ... | yes _ = 0ℤ
    ... | no ¬p = (num ℤ./ den) ⦃ ℤ.≢-nonZero ¬p ⦄
ℰ⟦ ChoiceValue c ⟧ _ s = choices s ‼d c
ℰ⟦ TimeIntervalStart ⟧ e _ = + getPosixTime (startTime (timeInterval e))
ℰ⟦ TimeIntervalEnd ⟧ e _ = + getPosixTime (endTime (timeInterval e))
ℰ⟦ UseValue v ⟧ _ s = boundValues s ‼d v
ℰ⟦ Cond o x y ⟧ e s = if 𝒪⟦ o ⟧ e s then ℰ⟦ x ⟧ e s else ℰ⟦ y ⟧ e s
```

### Observation

```agda
𝒪⟦ AndObs x y ⟧ e s = 𝒪⟦ x ⟧ e s ∧ 𝒪⟦ y ⟧ e s
𝒪⟦ OrObs x y ⟧ e s = 𝒪⟦ x ⟧ e s ∨ 𝒪⟦ y ⟧ e s
𝒪⟦ NotObs x ⟧ e s = not (𝒪⟦ x ⟧ e s)
𝒪⟦ ChoseSomething c ⟧  _ s = ⌊ c ∈ᵐ? choices s ⌋
𝒪⟦ ValueGE y x ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≤? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueGT y x ⟧ e s = ⌊ ℰ⟦ x ⟧ e s <? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueLT x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s <? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueLE x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≤? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueEQ x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≟ ℰ⟦ y ⟧ e s ⌋
𝒪⟦ TrueObs ⟧ _ _ = true
𝒪⟦ FalseObs ⟧ _ _ = false
```
