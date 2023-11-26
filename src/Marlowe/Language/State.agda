module Marlowe.Language.State where

open import Agda.Builtin.Int using (Int)
open import Contrib.Data.List.AssocList
open import Contrib.Data.Nat.Properties
open import Data.Bool using (Bool; _∧_; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.List.Relation.Unary.Any using (lookup; _─_; _∷=_; here; there; index)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (case_of_; _∘_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)

open import Marlowe.Language.Contract
open PosixTime using (getPosixTime)

open Decidable _≟-AccountId×Token_ renaming (_↑_ to _↑-AccountId×Token_)

record State : Set where
  constructor ⟨_,_,_,_⟩
  field
    accounts : AssocList (AccountId × Token) ℕ
    choices : AssocList ChoiceId Int
    boundValues : AssocList ValueId Int
    minTime : PosixTime

emptyState : PosixTime → State
emptyState m = ⟨ [] , [] , [] , m ⟩

record TimeInterval : Set where
  constructor mkInterval
  field
    startTime : PosixTime
    offset : ℕ

endTime : TimeInterval → PosixTime
endTime (mkInterval (mkPosixTime s) o) = mkPosixTime (s + o)

record Environment : Set where
  constructor mkEnvironment
  field
    timeInterval : TimeInterval

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
