module Contrib.Data.Nat.Properties where

open import Data.Nat
open import Data.Nat.Properties

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl; sym; trans)

m+[n+o]≡n+[m+o] : ∀ (m n o : ℕ) → m + (n + o) ≡ n + (m + o)
m+[n+o]≡n+[m+o] m n o =
  let s₁ = sym (cong (_+ o) (+-comm n m))
      s₂ = +-assoc m n o
      s₃ = +-assoc n m o
  in trans (trans (sym s₂) s₁) s₃

m+n+o≡n+[m+o] : ∀ {m n o : ℕ} → m + n + o ≡ n + (m + o)
m+n+o≡n+[m+o] {m} {n} {o} =
  let s₁ = sym (cong (_+ o) (+-comm n m))
      s₂ = +-assoc n m o
  in trans s₁ s₂

m≤n⇒m+o≤n+o : ∀ {m n} o → m ≤ n → m + o ≤ n + o
m≤n⇒m+o≤n+o {n = n} o z≤n = m≤n+m o n
m≤n⇒m+o≤n+o o (s≤s r) = s≤s (m≤n⇒m+o≤n+o o r)

m∸n≡m∸[m⊓n] : ∀ {m n} → m ∸ n ≡ m ∸ m ⊓ n
m∸n≡m∸[m⊓n] {zero} {zero} = refl
m∸n≡m∸[m⊓n] {zero} {suc n} = refl
m∸n≡m∸[m⊓n] {suc m} {zero} = refl
m∸n≡m∸[m⊓n] {suc m} {suc n} = m∸n≡m∸[m⊓n] {m} {n}

o≤m⇛m∸o+[o+n]≡m+n : ∀ {m n o : ℕ} → o ≤ m → m ∸ o + (o + n) ≡ m + n
o≤m⇛m∸o+[o+n]≡m+n {m} {n} {zero} z≤n = refl
o≤m⇛m∸o+[o+n]≡m+n {suc m} {n} {suc o} (s≤s p) =
  trans (+-suc (m ∸ o) (o + n)) (cong suc (o≤m⇛m∸o+[o+n]≡m+n {m} {n} {o} p))
