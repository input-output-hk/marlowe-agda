---
title: Marlowe.Semantics.Operate.Properties
layout: page
---

```
open import Relation.Binary using (DecidableEquality)

module Marlowe.Semantics.Operate.Properties
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where
```

<!--
## Imports

```
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_)
open import Data.Product using (_,_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Marlowe.Language
open Entities-Parameterized-by-Party {Party}
open Entities-Parameterized-by-Token {Token}

open import Marlowe.Semantics.Operate _≟-Party_ _≟-Token_
open import Marlowe.Semantics.Reduce _≟-Party_ _≟-Token_

open Configuration
open TransactionInput
open Result

open import Marlowe.Semantics.Reduce.Properties _≟-Party_ _≟-Token_
```
-->

## Close is safe

Computing a transaction on a `Close` contract does not produce any warnings.

```
⇓-Close-is-safe : ∀ {s r}
  → (Close , s) ⇓ r
    ---------------
  → warnings r ≡ []
⇓-Close-is-safe (done _) = refl
⇓-Close-is-safe (reduce-until-quiescent refl refl x q y)
  rewrite ⇀⋆Close-is-terminal x rewrite ⇓-Close-is-safe y =
    trans (cong convertReduceWarnings (sym (⇀⋆Close-is-safe x))) refl
```

## Timed-out transaction closes contract

```
{- TODO
⇓-after-timeout-closes-contract : ∀ {c s tₛ Δₜ is r i}
  → maxTimeout c < tₛ
  → ⇓-eval c s ((mkTransactionInput (mkInterval (mkPosixTime tₛ) Δₜ) i) ∷ is) ≡ inj₁ r
⇓-after-timeout-closes-contract {c} {s} {tₛ} {Δₜ} {is} {r} {i} x with ⇓-eval c s ((mkTransactionInput (mkInterval (mkPosixTime tₛ) Δₜ) i) ∷ is)
... | inj₁ (r , reduce-until-quiescent x₁ x₂ x₃ x₄ snd) = {!!}
... | inj₁ (r , apply-input tₑ<t x₁ x₂ snd) = {!!}
... | inj₁ (r , done x₁) = {!!}
... | inj₂ y = {!!}
-}
```

## Transaction bound

```
inputsToTransactions : TimeInterval → List Input → List TransactionInput
inputsToTransactions ti []       = mkTransactionInput ti [] ∷ []
inputsToTransactions ti (h ∷ []) = mkTransactionInput ti (h ∷ []) ∷ []
inputsToTransactions ti (h ∷ t)  = mkTransactionInput ti (h ∷ []) ∷ inputsToTransactions ti t 

traceListToSingleInput : List TransactionInput → List TransactionInput
traceListToSingleInput [] = []
traceListToSingleInput (mkTransactionInput ti x ∷ t) = inputsToTransactions ti x ++ traceListToSingleInput t 

{-
traceToSingleInputIsEquivalent :
  ∀ {c s is}
  → ⇓-eval c s is ≡ ⇓-eval c s (traceListToSingleInput is)
traceToSingleInputIsEquivalent {c} {s} {[]} = refl
traceToSingleInputIsEquivalent {c} {s} {mkTransactionInput ti i ∷ is} = {!!}
-}
```
