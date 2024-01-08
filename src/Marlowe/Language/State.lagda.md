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
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)

open import Marlowe.Language.Contract as Contract using (PosixTime; mkPosixTime; ValueId)
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
  {Party : Set}
  {Token : Set}
  where

  open Contract.Parameterized {Party} {Token}
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
