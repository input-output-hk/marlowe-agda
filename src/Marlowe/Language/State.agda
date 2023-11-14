module Marlowe.Language.State where

open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; _∧_)
open import Data.List using (List; []; _∷_; sum; filter; map)
open import Data.List.Relation.Unary.Any using (lookup; _─_; _∷=_; here; there)
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

accountsTotal : AssocList (AccountId × Token) ℕ → ℕ
accountsTotal = sum ∘ map proj₂

totalₜ : Token → AssocList (AccountId × Token) ℕ → ℕ
totalₜ t = accountsTotal ∘ filter ((t ≟-Token_) ∘ proj₂ ∘ proj₁)

-- FIXME: proofs
postulate
  increaseValue : ∀ {a : AccountId} {t : Token} {abs : AssocList (AccountId × Token) ℕ} {n : ℕ} {p : (a , t) ∈ abs}
    → accountsTotal (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) + n)) ≡ accountsTotal abs + n

  decreaseValue : ∀ {a : AccountId} {t : Token} {abs : AssocList (AccountId × Token) ℕ} {n : ℕ} {p : (a , t) ∈ abs}
    → accountsTotal (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) ∸ n)) ≡ accountsTotal abs ∸ (proj₂ (lookup p) ⊓ n)

  constValue : ∀ {a₁ a₂ : AccountId} {t : Token} {abs : AssocList (AccountId × Token) ℕ} {n : ℕ} {p : (a₁ , t) ∈ abs}
    → accountsTotal abs ≡ accountsTotal (((a₂ , t) , (proj₂ (lookup p) ⊓ n)) ↑-AccountId×Token (p ∷= (proj₁ (lookup p) , proj₂ (lookup p) ∸ n)))

  monusElim : ∀ {a b x : ℕ} → a ∸ x + (x + b) ≡ a + b
