
module Primitives where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Bool using (Bool; false; true; if_then_else_; _∨_)
open import Data.String as String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Unary.Any using (Any; any?; lookup)
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
    getPosixTime : Int

-- see also: https://stackoverflow.com/questions/58705398/is-there-an-associative-list-in-the-standard-library
AssocList : Set → Set → Set
AssocList A B = List (A × B)

private
  variable
    A B : Set

_∈_ : A → AssocList A B → Set
a ∈ abs = Any ((a ≡_) ∘ proj₁) abs

module Decidable {A : Set} (_≟_ : DecidableEquality A) where

  _∈?_ : Decidable (_∈_ {A} {B})
  a ∈? abs = any? ((a ≟_) ∘ proj₁) abs

  _‼_ : (a : A) (abs : AssocList A B) → Maybe B
  a ‼ abs with a ∈? abs
  ... | yes p = just (proj₂ (lookup p))
  ... | no ¬p = nothing

postulate
  _↑_ : (p : A × B) (abs : AssocList A B) → AssocList A B
  _↓_ : (a : A) (abs : AssocList A B) → AssocList A B


record Map (K V : Set) : Set where
  constructor _via_
  field
    pairs : List (K × V)
    eqKey : K → K → Bool
    

emptyMap : {K V : Set} → (K → K → Bool) → Map K V
emptyMap eq = [] via eq


nullMap : {K V : Set} → Map K V → Bool
nullMap {K} {V} m =
  nullMap' (Map.pairs m)
    where
      nullMap' : List (K × V) → Bool
      nullMap' [] = true
      nullMap' _ = false

_member_ : {K V : Set} → K → Map K V → Bool
_member_ {K} {V} k m =
  member' (Map.pairs m)
    where
      _eq_ = Map.eqKey m
      member' : List (K × V) → Bool
      member' [] = false
      member' ((k' , _) ∷ xs) = k eq k' ∨ member' xs

_lookup_ : {K V : Set} → K → Map K V → Maybe V
_lookup_ {K} {V} k m =
  lookup' (Map.pairs m)
    where
      _eq_ = Map.eqKey m
      lookup' : List (K × V) → Maybe V
      lookup' [] = nothing
      lookup' ((k' , v') ∷ xs) = if k eq k' then just v' else lookup' xs

_lookup_default_ : {K V : Set} → K → Map K V → V → V
_lookup_default_ {K} {V} k m v =
  lookup' (Map.pairs m)
    where
      _eq_ = Map.eqKey m
      lookup' : List (K × V) → V
      lookup' [] = v
      lookup' ((k' , v') ∷ xs) = if k eq k' then v' else lookup' xs

_delete_ : {K V : Set} → K → Map K V → Map K V
_delete_ {K} {V} k m =
  record m {pairs = delete' (Map.pairs m)}
    where
      _eq_ = Map.eqKey m
      delete' : List (K × V) → List (K × V)
      delete' [] = []
      delete' (x ∷ xs) = if k eq proj₁ x then delete' xs else x ∷ delete' xs

_insert_into_ : {K V : Set} → K → V → Map K V → Map K V
_insert_into_ {K} {V} k v m =
  record m {pairs = record {fst = k; snd = v} ∷ delete' (Map.pairs m)}
    where
      _eq_ = Map.eqKey m
      delete' : List (K × V) → List (K × V)
      delete' [] = []
      delete' (x ∷ xs) = if k eq proj₁ x then delete' xs else x ∷ delete' xs
