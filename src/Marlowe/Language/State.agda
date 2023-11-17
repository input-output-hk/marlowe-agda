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

accountsΣ : AssocList (AccountId × Token) ℕ → ℕ
accountsΣ = sum ∘ map proj₂

totalₜ : Token → AssocList (AccountId × Token) ℕ → ℕ
totalₜ t = accountsΣ ∘ filter ((t ≟-Token_) ∘ proj₂ ∘ proj₁)

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

accountsΣ-∷ :
  ∀ {n : ℕ}
    {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  ---------------------------------------------------------------------------
  → accountsΣ ((a×t , n) ∷ abs) ≡ n + accountsΣ abs
accountsΣ-∷ {zero} = refl
accountsΣ-∷ {suc n} {a×t} {abs} rewrite accountsΣ-∷ {n} {a×t} {abs} = refl

accountsΣ-∷′ :
  ∀ {m n : ℕ}
    {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  ---------------------------------------------------------------------------
  → accountsΣ ((a×t , m + n) ∷ abs) ≡ n + accountsΣ ((a×t , m) ∷ abs)
accountsΣ-∷′ {m} {zero} {a×t} {abs} rewrite +-identityʳ m = refl
accountsΣ-∷′ {m} {suc n} {a×t} {abs} rewrite accountsΣ-∷′ {m} {n} {a×t} {abs} =
 trans
   (cong (_+ accountsΣ abs) (+-comm m (suc n)))
   (cong suc (+-assoc n m (accountsΣ abs)))

accountsΣ-↑ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  ----------------------------------------------------------------------------------------
  → accountsΣ (p ∷= (a×t , proj₂ (lookup p) + n)) ≡ n + accountsΣ abs
accountsΣ-↑ {a×t} {x ∷ xs} {n} (here refl) = accountsΣ-∷′ {proj₂ x} {n} {a×t} {xs}
accountsΣ-↑ {a×t} {x ∷ xs} {n} (there p) rewrite accountsΣ-↑ {a×t} {xs} {n} p
  = sym (m+[n+o]≡n+[m+o] n (proj₂ x) (accountsΣ xs))

accountsΣ-─ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  ---------------------------------------------------------------------------
  → accountsΣ (p ∷= (proj₁ (lookup p) , n)) ≡ n + accountsΣ (abs ─ p)
accountsΣ-─ {a×t} {abs = x ∷ xs} {n} (here refl) = refl
accountsΣ-─ {a×t} {abs = x ∷ xs} {n} (there p)
  rewrite accountsΣ-─ {a×t} {xs} {n} p =
    m+[n+o]≡n+[m+o] (proj₂ x) n (accountsΣ (xs ─ p))

accountsΣ-↓↑ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
  → (p : a×t ∈ abs)
  --------------------------------------------------------------------------------
  → accountsΣ abs ≡ accountsΣ (p ∷= (proj₁ (lookup p) , proj₂ (lookup p)))
accountsΣ-↓↑ (here refl) = refl
accountsΣ-↓↑ {a×t} {abs = x ∷ xs} (there p) rewrite accountsΣ-↓↑ {a×t} {xs} p = refl

accountsΣ-≤ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  -------------------------------------------------
  → n ≤ accountsΣ (p ∷= (proj₁ (lookup p) , n))
accountsΣ-≤ {a×t} {abs} {n} p =
  let s₁ = m≤m+n n (accountsΣ (abs ─ p))
      s₂ = ≤-reflexive (sym (accountsΣ-─ {a×t} {abs} {n} p))
  in ≤-trans s₁ s₂

accountsΣ-↓≤ :
  ∀ {a×t : AccountId × Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : a×t ∈ abs)
  ------------------------------------------------------------------------------------
  → accountsΣ (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) ⊓ n)) ≤ accountsΣ abs
accountsΣ-↓≤ {a×t} {abs} {n} p =
  let s₁ = ≤-reflexive (accountsΣ-─ {a×t} {abs} {n = proj₂ (lookup p) ⊓ n} p)
      s₂ = ≤-reflexive (sym (accountsΣ-─ {a×t} {abs} {n = proj₂ (lookup p)} p))
      s₃ = m⊓n≤m (proj₂ (lookup p)) n
      s₄ = m≤n⇒m+o≤n+o (accountsΣ (abs ─ p)) s₃
      s₅ = ≤-reflexive (sym (accountsΣ-↓↑ {a×t} {abs} p))
  in ≤-trans (≤-trans s₁ s₄) (≤-trans s₂ s₅)

accountsΣ-↓ :
  ∀ {a : AccountId}
    {t : Token}
    {abs : AssocList (AccountId × Token) ℕ}
    {n : ℕ}
  → (p : (a , t) ∈ abs)
  -------------------------------------------------------------------------------------------------------------
  → accountsΣ (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) ∸ n)) ≡ accountsΣ abs ∸ (proj₂ (lookup p) ⊓ n)
accountsΣ-↓ {a} {t} {((_ , m) ∷ xs)} {n} (here refl) =
  let s₁ = cong (_+ accountsΣ xs) (m∸n≡m∸[m⊓n] {m} {n})
      s₂ = +-∸-comm {m} (accountsΣ xs) {m ⊓ n} (m⊓n≤m m n)
   in trans s₁ (sym s₂)
accountsΣ-↓ {a} {t} {x ∷ xs} {n} (there p) rewrite accountsΣ-↓ {a} {t} {abs = xs} {n} p =
  let m = proj₂ (lookup p)
      s₁ = accountsΣ-≤ {(a , t)} {xs} {m ⊓ n} p
      s₂ = accountsΣ-↓≤ {(a , t)} {xs} {n} p
  in sym (+-∸-assoc (proj₂ x) {accountsΣ xs} {m ⊓ n} (≤-trans s₁ s₂))
