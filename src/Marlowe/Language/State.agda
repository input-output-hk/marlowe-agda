module Marlowe.Language.State where

open import Agda.Builtin.Int using (Int)
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
open PosixTime using (getPosixTime)

open import Primitives
open Decidable _≟-AccountId×Token_ renaming (_↑_ to _↑-AccountId×Token_)

record State : Set where
  constructor mkState
  field
    accounts : AssocList (AccountId × Token) ℕ
    choices : AssocList ChoiceId Int
    boundValues : AssocList ValueId Int
    minTime : PosixTime

emptyState : PosixTime → State
emptyState = mkState [] [] []

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

Σ-accounts : AssocList (AccountId × Token) ℕ → ℕ
Σ-accounts = sum ∘ map proj₂

totalₜ : Token → AssocList (AccountId × Token) ℕ → ℕ
totalₜ t = Σ-accounts ∘ filter ((t ≟-Token_) ∘ proj₂ ∘ proj₁)

_↑-update_ : (p : (AccountId × Token) × ℕ) (abs : AssocList (AccountId × Token) ℕ) → AssocList (AccountId × Token) ℕ
(a , b) ↑-update abs with a ∈? abs
... | yes p = p ∷= (a , proj₂ (lookup p) + b)
... | no _ = (a , b) ∷ abs

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

m<n⇒m⊓n≡m : ∀ {m n} → m < n → m ⊓ n ≡ m
m<n⇒m⊓n≡m m<n = m≤n⇒m⊓n≡m (<⇒≤ m<n)

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

Σ-accounts-∷ :
  ∀ {n : ℕ}
    {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  ---------------------------------------------------------------------------
  → Σ-accounts ((a×t , n) ∷ abs) ≡ n + Σ-accounts abs
Σ-accounts-∷ {zero} = refl
Σ-accounts-∷ {suc n} {a×t} {abs} rewrite Σ-accounts-∷ {n} {a×t} {abs} = refl

Σ-accounts-∷′ :
  ∀ {m n : ℕ}
    {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  ---------------------------------------------------------------------------
  → Σ-accounts ((a×t , m + n) ∷ abs) ≡ n + Σ-accounts ((a×t , m) ∷ abs)
Σ-accounts-∷′ {m} {zero} {a×t} {abs} rewrite +-identityʳ m = refl
Σ-accounts-∷′ {m} {suc n} {a×t} {abs} rewrite Σ-accounts-∷′ {m} {n} {a×t} {abs} =
 trans
   (cong (_+ Σ-accounts abs) (+-comm m (suc n)))
   (cong suc (+-assoc n m (Σ-accounts abs)))

Σ-accounts-↑ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  ----------------------------------------------------------------------------------------
  → Σ-accounts (p ∷= (a×t , proj₂ (lookup p) + n)) ≡ n + Σ-accounts abs
Σ-accounts-↑ {a×t} {x ∷ xs} {n} (here refl) = Σ-accounts-∷′ {proj₂ x} {n} {a×t} {xs}
Σ-accounts-↑ {a×t} {x ∷ xs} {n} (there p) rewrite Σ-accounts-↑ {a×t} {xs} {n} p
  = sym (m+[n+o]≡n+[m+o] n (proj₂ x) (Σ-accounts xs))

Σ-accounts-─ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  ---------------------------------------------------------------------------
  → Σ-accounts (p ∷= (proj₁ (lookup p) , n)) ≡ n + Σ-accounts (abs ─ p)
Σ-accounts-─ {a×t} {abs = x ∷ xs} {n} (here refl) = refl
Σ-accounts-─ {a×t} {abs = x ∷ xs} {n} (there p)
  rewrite Σ-accounts-─ {a×t} {xs} {n} p =
    m+[n+o]≡n+[m+o] (proj₂ x) n (Σ-accounts (xs ─ p))

Σ-accounts-↓↑ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (p : a×t ∈ abs)
  --------------------------------------------------------------------------------
  → Σ-accounts abs ≡ Σ-accounts (p ∷= (proj₁ (lookup p) , proj₂ (lookup p)))
Σ-accounts-↓↑ (here refl) = refl
Σ-accounts-↓↑ {a×t} {abs = x ∷ xs} (there p) rewrite Σ-accounts-↓↑ {a×t} {xs} p = refl

Σ-accounts-≤ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  -------------------------------------------------
  → n ≤ Σ-accounts (p ∷= (proj₁ (lookup p) , n))
Σ-accounts-≤ {a×t} {abs} {n} p =
  let s₁ = m≤m+n n (Σ-accounts (abs ─ p))
      s₂ = ≤-reflexive (sym (Σ-accounts-─ {a×t} {abs} {n} p))
  in ≤-trans s₁ s₂

Σ-accounts-↓≤ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  ------------------------------------------------------------------------------------
  → Σ-accounts (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) ⊓ n)) ≤ Σ-accounts abs
Σ-accounts-↓≤ {a×t} {abs} {n} p =
  let s₁ = ≤-reflexive (Σ-accounts-─ {a×t} {abs} {n = proj₂ (lookup p) ⊓ n} p)
      s₂ = ≤-reflexive (sym (Σ-accounts-─ {a×t} {abs} {n = proj₂ (lookup p)} p))
      s₃ = m⊓n≤m (proj₂ (lookup p)) n
      s₄ = m≤n⇒m+o≤n+o (Σ-accounts (abs ─ p)) s₃
      s₅ = ≤-reflexive (sym (Σ-accounts-↓↑ {a×t} {abs} p))
  in ≤-trans (≤-trans s₁ s₄) (≤-trans s₂ s₅)

Σ-accounts-↓ :
  ∀ {a : AccountId}
    {t : Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : (a , t) ∈ abs)
  -------------------------------------------------------------------------------------------------------------
  → Σ-accounts (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) ∸ n)) ≡ Σ-accounts abs ∸ (proj₂ (lookup p) ⊓ n)
Σ-accounts-↓ {a} {t} {((_ , m) ∷ xs)} {n} (here refl) =
  let s₁ = cong (_+ Σ-accounts xs) (m∸n≡m∸[m⊓n] {m} {n})
      s₂ = +-∸-comm {m} (Σ-accounts xs) {m ⊓ n} (m⊓n≤m m n)
   in trans s₁ (sym s₂)
Σ-accounts-↓ {a} {t} {x ∷ xs} {n} (there p) rewrite Σ-accounts-↓ {a} {t} {abs = xs} {n} p =
  let m = proj₂ (lookup p)
      s₁ = Σ-accounts-≤ {(a , t)} {xs} {m ⊓ n} p
      s₂ = Σ-accounts-↓≤ {(a , t)} {xs} {n} p
  in sym (+-∸-assoc (proj₂ x) {Σ-accounts xs} {m ⊓ n} (≤-trans s₁ s₂))
