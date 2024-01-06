---
title: Marlowe.Language.State.Properties
layout: page
---

```
open import Relation.Binary using (DecidableEquality)

module Marlowe.Language.State.Properties
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where
```

## Imports

```
open import Agda.Builtin.Int using (Int)
open import Contrib.Data.Nat.Properties
open import Data.Bool using (Bool; _∧_; true; false)
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

open import Contrib.Data.List.AssocList
open import Marlowe.Language.Contract as C
open import Marlowe.Language.State as S
open import Marlowe.Language.Transaction as T
open PosixTime using (getPosixTime)

open C.Parameterized _≟-Party_ _≟-Token_
open S.Parameterized _≟-Party_ _≟-Token_
open T.Parameterized _≟-Party_ _≟-Token_

open Decidable _≟-AccountId×Token_ renaming (_↑_ to _↑-AccountId×Token_)
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

projₚ : Token → Payment → ℕ
projₚ t (a [ t′ , n ]↦ _) = 1ₜ t (t′ , n)

Σ-payments : Token → List Payment → ℕ
Σ-payments t = sum ∘ map (projₚ t)
```

```
zero-projₜ : ∀ {a×t : AccountId × Token} {t : Token} → projₜ t (a×t , 0) ≡ 0
zero-projₜ {a×t} {t} with ⌊ t ≟-Token (proj₂ a×t) ⌋
... | true = refl
... | false = refl

linear-projₜ :
  ∀ {a×t : AccountId × Token}
    {t : Token}
    {m n : ℕ}
  → ((projₜ t (a×t , m)) + (projₜ t (a×t , n))) ≡ projₜ t (a×t , m + n)
linear-projₜ {a×t} {t} with ⌊ t ≟-Token (proj₂ a×t) ⌋
... | true = refl
... | false = refl

⊓-projₜ : ∀ {t} {a×t : AccountId × Token} {m n} → projₜ t (a×t , m ⊓ n) ≡ projₜ t (a×t , m) ⊓ projₜ t (a×t , n)
⊓-projₜ {t} {a×t} with ⌊ t ≟-Token (proj₂ a×t) ⌋
... | true = refl
... | false = refl

∸-projₜ : ∀ {t} {a×t : AccountId × Token} {m n} → projₜ t (a×t , m ∸ n) ≡ projₜ t (a×t , m) ∸ projₜ t (a×t , n)
∸-projₜ {t₁} {a×t} with ⌊ t₁ ≟-Token (proj₂ a×t) ⌋
... | true = refl
... | false = refl

Σ-accounts-─ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (t : Token)
  → (a×t∈abs : a×t ∈ abs)
  ------------------------------------------------------------------------------------------
  → Σ-accounts t abs ≡ projₜ t (a×t , proj₂ (lookup a×t∈abs)) + Σ-accounts t (abs ─ a×t∈abs)
Σ-accounts-─ t (here refl) = refl
Σ-accounts-─ {a×t} {abs = x ∷ xs} t (there a×t∈abs) rewrite Σ-accounts-─ {abs = xs} t a×t∈abs =
  m+[n+o]≡n+[m+o] (projₜ t x) (projₜ t (a×t , proj₂ (lookup a×t∈abs))) (Σ-accounts t (xs ─ a×t∈abs))

Σ-accounts-↓≤ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (t : Token)
  → (a×t∈abs : a×t ∈ abs)
  -----------------------------------------------------------
  → projₜ t (a×t , proj₂ (lookup a×t∈abs)) ≤ Σ-accounts t abs
Σ-accounts-↓≤ {a×t} {abs} t a×t∈abs =
  ≤-trans
    (m≤m+n (projₜ t (a×t , proj₂ (lookup a×t∈abs))) (Σ-accounts t (abs ─ a×t∈abs)))
    (≤-reflexive (sym (Σ-accounts-─ t a×t∈abs)))

Σ-accounts-↓≤⊓ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (n : ℕ)
  → (t : Token)
  → (a×t∈abs : a×t ∈ abs)
  -----------------------------------------------------------------
  → (projₜ t (a×t , proj₂ (lookup a×t∈abs) ⊓ n)) ≤ Σ-accounts t abs
Σ-accounts-↓≤⊓ {a×t} n t a×t∈abs =
  ≤-trans
    (≤-trans
      (≤-reflexive (⊓-projₜ {t} {a×t}))
      (m⊓n≤m (projₜ t (a×t , proj₂ (lookup a×t∈abs))) (projₜ t (a×t , n))))
    (Σ-accounts-↓≤ t a×t∈abs)

Σ-accounts-↑ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (n : ℕ)
  → (t : Token)
  → (a×t∈abs : a×t ∈ abs)
  -----------------------------------------------------------------------------------------------------
  → Σ-accounts t (a×t∈abs ∷= (a×t , proj₂ (lookup a×t∈abs) + n)) ≡ projₜ t (a×t , n) + Σ-accounts t abs
Σ-accounts-↑ {a×t} {(_ , m) ∷ xs} n f (here refl) = Σ-accounts-∷ m n {a×t} {xs} f
  where
    Σ-accounts-∷ : ∀ (m n : ℕ) {a×t : AccountId × Token} {abs : AssocList (AccountId × Token) ℕ}
                    → (t : Token)
                    → Σ-accounts t ((a×t , m + n) ∷ abs) ≡ projₜ t (a×t , n) + Σ-accounts t ((a×t , m) ∷ abs)
    Σ-accounts-∷ m zero {a×t} t rewrite +-identityʳ m rewrite zero-projₜ {a×t} {t} = refl
    Σ-accounts-∷ m (suc n) {a×t} {abs} t
      rewrite Σ-accounts-∷ m n {a×t} {abs} t
      rewrite sym (+-assoc (projₜ t (a×t , suc n)) (projₜ t (a×t , m)) (Σ-accounts t abs))
      rewrite sym (+-comm (projₜ t (a×t , m)) (projₜ t (a×t , suc n)))
      rewrite linear-projₜ {a×t} {t} {m} {suc n} = refl
Σ-accounts-↑ {a×t} {abs = x ∷ xs} n t (there p) rewrite Σ-accounts-↑ {abs = xs} n t p
  = sym (m+[n+o]≡n+[m+o] (projₜ t (a×t , n)) (projₜ t x) (Σ-accounts t xs))

Σ-accounts-↓ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (n : ℕ)
  → (t : Token)
  → (a×t∈abs : a×t ∈ abs)
  --------------------------------------------------------------------------------------------------------------------------------
  → Σ-accounts t (a×t∈abs ∷= (a×t , proj₂ (lookup a×t∈abs) ∸ n)) ≡ Σ-accounts t abs ∸ (projₜ t (a×t , proj₂ (lookup a×t∈abs) ⊓ n))
Σ-accounts-↓ {a×t} {(x ∷ xs)} n t (here refl) =
   trans
     (trans
       (trans
         (cong (_+ Σ-accounts t xs) (∸-projₜ {t} {a×t} {proj₂ x} {n}))
         (cong (_+ Σ-accounts t xs) (m∸n≡m∸[m⊓n] {projₜ t x} {projₜ t (a×t , n)})))
       (sym (+-∸-comm (Σ-accounts t xs) (m⊓n≤m (projₜ t x) (projₜ t (a×t , n))))))
     (sym (cong (projₜ t x + Σ-accounts t xs ∸_) (⊓-projₜ {t} {a×t} {proj₂ x} {n})))
Σ-accounts-↓ {a×t} {abs = x ∷ xs} n t (there p) rewrite Σ-accounts-↓ {a×t} {abs = xs} n t p =
  sym (+-∸-assoc (projₜ t x) (Σ-accounts-↓≤⊓ n t p))
```
