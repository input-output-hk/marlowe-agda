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
open import Data.Product.Properties using (≡-dec)
open import Function.Base using (_∘_)

open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Marlowe.Language.Contract as Contract using (PosixTime; mkPosixTime)
```


## Environment

```
record TimeInterval : Set where
  constructor mkInterval
  field
    startTime : PosixTime
    offset : ℕ

endTime : TimeInterval → PosixTime
endTime (mkInterval (mkPosixTime s) o) = mkPosixTime (s + o)
```

```
record Environment : Set where
  constructor mkEnvironment
  field
    timeInterval : TimeInterval

interval-end : Environment → ℕ
interval-end (mkEnvironment (mkInterval (mkPosixTime s) o)) = s + o
```

```
module Parameterized
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where

  open Contract.Parameterized _≟-Party_ _≟-Token_
  open Decidable (≡-dec _≟-AccountId_ _≟-Token_)
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

### Account updates

```
  _↑-update_ : (p : (AccountId × Token) × ℕ) (abs : AssocList (AccountId × Token) ℕ) → AssocList (AccountId × Token) ℕ
  (a , b) ↑-update abs with a ∈? abs
  ... | yes p = p ∷= (a , proj₂ (lookup p) + b)
  ... | no _ = (a , b) ∷ abs
```
