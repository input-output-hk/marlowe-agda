module Marlowe.Language.State.Properties where

open import Agda.Builtin.Int using (Int)
open import Contrib.Data.Nat.Properties
open import Data.Bool using (Bool; _∧_)
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.List.Relation.Unary.Any using (lookup; _─_; _∷=_; here; there; index)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (case_of_; _∘_)

open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)

open import Marlowe.Language.Contract
open import Marlowe.Language.State
open PosixTime using (getPosixTime)

open import Contrib.Data.List.AssocList
open Decidable _≟-AccountId×Token_ renaming (_↑_ to _↑-AccountId×Token_)

Σ-accounts-─ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (p : a×t ∈ abs)
  -----------------------------------------------------------
  → Σ-accounts abs ≡ (proj₂ (lookup p)) + Σ-accounts (abs ─ p)
Σ-accounts-─ {a×t} {abs = x ∷ xs} (here refl) = refl
Σ-accounts-─ {a×t} {abs = x ∷ xs} (there p) rewrite Σ-accounts-─ {a×t} {xs} p =
  m+[n+o]≡n+[m+o] (proj₂ x) (proj₂ (lookup p)) (Σ-accounts (xs ─ p))

Σ-accounts-↓≤ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (p : a×t ∈ abs)
  -----------------------------------------
  → (proj₂ (lookup p)) ≤ Σ-accounts abs
Σ-accounts-↓≤ {a×t} {abs} p =
  ≤-trans (m≤m+n (proj₂ (lookup p)) (Σ-accounts (abs ─ p))) (≤-reflexive (sym (Σ-accounts-─ p)))

Σ-accounts-↓≤⊓ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (n : ℕ)
  → (p : a×t ∈ abs)
  -----------------------------------------
  → (proj₂ (lookup p) ⊓ n) ≤ Σ-accounts abs
Σ-accounts-↓≤⊓ {a×t} {abs} n p = ≤-trans (m⊓n≤m (proj₂ (lookup p)) n) (Σ-accounts-↓≤ p)

Σ-accounts-↑ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (n : ℕ)
  → (p : a×t ∈ abs)
  ---------------------------------------------------------------------
  → Σ-accounts (p ∷= (a×t , proj₂ (lookup p) + n)) ≡ n + Σ-accounts abs
Σ-accounts-↑ {a×t} {x ∷ xs} n (here refl) = Σ-accounts-∷ (proj₂ x) n {a×t} {xs}
  where
    Σ-accounts-∷ : ∀ (m n : ℕ) {a×t : AccountId × Token} {abs : AssocList (AccountId × Token) ℕ}
                    → Σ-accounts ((a×t , m + n) ∷ abs) ≡ n + Σ-accounts ((a×t , m) ∷ abs)
    Σ-accounts-∷ m zero rewrite +-identityʳ m = refl
    Σ-accounts-∷ m (suc n) {a×t} {abs} rewrite Σ-accounts-∷ m n {a×t} {abs} =
      trans (cong (_+ Σ-accounts abs) (+-comm m (suc n))) (cong suc (+-assoc n m (Σ-accounts abs)))
Σ-accounts-↑ {abs = x ∷ xs} n (there p) rewrite Σ-accounts-↑ {abs = xs} n p
  = sym (m+[n+o]≡n+[m+o] n (proj₂ x) (Σ-accounts xs))

Σ-accounts-↓ :
  ∀ {a : AccountId}
    {t : Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (n : ℕ)
  → (p : (a , t) ∈ abs)
  -------------------------------------------------------------------------------------------------------
  → Σ-accounts (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) ∸ n)) ≡ Σ-accounts abs ∸ (proj₂ (lookup p) ⊓ n)
Σ-accounts-↓ {abs = ((_ , m) ∷ xs)} n (here refl) =
  trans (cong (_+ Σ-accounts xs) (m∸n≡m∸[m⊓n] {m} {n})) (sym (+-∸-comm (Σ-accounts xs) (m⊓n≤m m n)))
Σ-accounts-↓ {abs = x ∷ xs} n (there p) rewrite Σ-accounts-↓ {abs = xs} n p =
  sym (+-∸-assoc (proj₂ x) (Σ-accounts-↓≤⊓ n p))
