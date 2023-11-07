module Primitives where

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.List.Relation.Unary.Any using (Any; any?; lookup)
open import Data.List.Relation.Unary.All using (All)
open import Function using (_∘_)
open import Relation.Binary using (Decidable; DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; _≡_; _≢_)
open import Relation.Nullary using (yes; no)

-- see also: https://stackoverflow.com/questions/58705398/is-there-an-associative-list-in-the-standard-library
AssocList : Set → Set → Set
AssocList A B = List (A × B)

private
  variable
    A B : Set

_∈_ : A → AssocList A B → Set
a ∈ abs = Any ((a ≡_) ∘ proj₁) abs

_∉_ : A → AssocList A B → Set
a ∉ abs = All ((a ≢_) ∘ proj₁) abs

module Decidable {A : Set} (_≟_ : DecidableEquality A) where

  _∈?_ : Decidable (_∈_ {A} {B})
  a ∈? abs = any? ((a ≟_) ∘ proj₁) abs

  _‼_ : (a : A) (abs : AssocList A B) → Maybe B
  a ‼ abs with a ∈? abs
  ... | yes p = just (proj₂ (lookup p))
  ... | no ¬p = nothing

  _‼_default_ : (a : A) (abs : AssocList A B) → (b : B) → B
  a ‼ abs default b = fromMaybe b (a ‼ abs)

  postulate
    isElem : ∀ {a : A} { abs : AssocList A B } {i} → (p : Any (λ x → i ≡ proj₁ x) abs) → just (proj₂ (lookup p)) ≡ (a ‼ abs)


postulate
  _↑_ : (p : A × B) (abs : AssocList A B) → AssocList A B
  _↓_ : (a : A) (abs : AssocList A B) → AssocList A B
