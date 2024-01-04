---
title: Marlowe.Language.State
layout: page
---

```
module Marlowe.Language.State where
```

## Imports

```
open import Contrib.Data.List.AssocList
open import Contrib.Data.Nat.Properties
open import Data.Bool using (Bool; _∧_; true; false; if_then_else_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.List.Relation.Unary.Any using (lookup; _∷=_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Marlowe.Language.Contract
open PosixTime using (getPosixTime)

open Decidable _≟-AccountId×Token_ renaming (_↑_ to _↑-AccountId×Token_)
```

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

```
1ₜ : Token → Token × ℕ → ℕ
1ₜ t₁ (t₂ , n) with ⌊ t₁ ≟-Token t₂ ⌋
... | true = n
... | false = 0

projₜ : Token → (AccountId × Token) × ℕ → ℕ
projₜ t ((_ , t′) , n) = 1ₜ t (t′ , n)

Σ-accounts : Token → AssocList (AccountId × Token) ℕ → ℕ
Σ-accounts t = sum ∘ map (projₜ t)

filter-accounts : Token → AssocList (AccountId × Token) ℕ → AssocList (AccountId × Token) ℕ
filter-accounts t = filter ((t ≟-Token_) ∘ proj₂ ∘ proj₁)

_↑-update_ : (p : (AccountId × Token) × ℕ) (abs : AssocList (AccountId × Token) ℕ) → AssocList (AccountId × Token) ℕ
(a , b) ↑-update abs with a ∈? abs
... | yes p = p ∷= (a , proj₂ (lookup p) + b)
... | no _ = (a , b) ∷ abs
```