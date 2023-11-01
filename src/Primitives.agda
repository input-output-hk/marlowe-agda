
module Primitives where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Bool using (Bool; false; true; if_then_else_; _∨_)
open import Data.String as String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.List.Relation.Unary.Any using (Any; any?; lookup)
open import Data.List.Relation.Unary.All using (All)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

record ByteString : Set where
  constructor mkByteString
  field
    getByteString : String

_eqByteString_ : ∀ (a b : ByteString) → Dec (a ≡ b)
_eqByteString_ (mkByteString x) (mkByteString y) with x String.≟ y
... | yes p = yes (cong mkByteString p)
... | no p = no (λ x →  p (cong ByteString.getByteString x))


record PosixTime : Set where
  constructor mkPosixTime
  field
    getPosixTime : ℕ

_<ᵖ_ : PosixTime → PosixTime → Set
_<ᵖ_ (mkPosixTime x) (mkPosixTime y) = x ℕ.< y

_≤ᵖ_ : PosixTime → PosixTime → Set
_≤ᵖ_ (mkPosixTime x) (mkPosixTime y) = x ℕ.≤ y

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
  _↑_ : (p : A × B) (abs : AssocList A B) → AssocList A B
  _↓_ : (a : A) (abs : AssocList A B) → AssocList A B
