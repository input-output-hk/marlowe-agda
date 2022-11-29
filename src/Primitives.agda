
module Primitives where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Bool using (Bool; false; if_then_else_; _∨_)
open import Data.String as String using (String)
open import Relation.Nullary.Decidable using (⌊_⌋)


data ByteString : Set where
  mkByteString : String → ByteString

unByteString : ByteString → String
unByteString (mkByteString x) = x

_eqByteString_ : ByteString → ByteString → Bool
_eqByteString_ (mkByteString x) (mkByteString y) =  ⌊ x String.≟ y ⌋


data PosixTime : Set where
  mkPosixTime : Int → PosixTime

unPosixTime : PosixTime → Int
unPosixTime (mkPosixTime x) = x


record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B


data Map (K V : Set) : Set where
  mkMap : List (Pair K V) → Map K V

_member_via_ : {K V : Set} → K → Map K V → (K → K → Bool) → Bool
_member_via_ {K} {V} k (mkMap m) _eq_ =
  member' m
    where
      member' : List (Pair K V) → Bool
      member' [] = false
      member' (x ∷ xs) = k eq Pair.fst x ∨ member' xs

_lookup_default_via_ : {K V : Set} → K → Map K V → V → (K → K → Bool) → V
_lookup_default_via_ {K} {V} k (mkMap m) v _eq_ =
  lookup' m
    where
      lookup' : List (Pair K V) → V
      lookup' [] = v
      lookup' (x ∷ xs) = if k eq Pair.fst x then Pair.snd x else lookup' xs
