
module Primitives where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Bool using (Bool; false; true; if_then_else_; _∨_)
open import Data.String as String using (String)
open import Relation.Nullary.Decidable using (⌊_⌋)


record ByteString : Set where
  constructor mkByteString
  field
    getByteString : String

_eqByteString_ : ByteString → ByteString → Bool
_eqByteString_ (mkByteString x) (mkByteString y) =  ⌊ x String.≟ y ⌋


record PosixTime : Set where
  constructor mkPosixTime
  field
    getPosixTime : Int


record Pair (A B : Set) : Set where
  constructor pair
  field
    fst : A
    snd : B


record Triple (A B C : Set) : Set where
  constructor triple
  field
    fst : A
    snd : B
    trd : C


record Map (K V : Set) : Set where
  constructor _via_
  field
    pairs : List (Pair K V)
    eqKey : K → K → Bool
    

nullMap :  {K V : Set} → Map K V → Bool
nullMap {K} {V} m =
  nullMap' (Map.pairs m)
    where
      nullMap' : List (Pair K V) → Bool
      nullMap' [] = true
      nullMap' _ = false

_member_ : {K V : Set} → K → Map K V → Bool
_member_ {K} {V} k m =
  member' (Map.pairs m)
    where
      _eq_ = Map.eqKey m
      member' : List (Pair K V) → Bool
      member' [] = false
      member' (pair k' _ ∷ xs) = k eq k' ∨ member' xs

_lookup_default_ : {K V : Set} → K → Map K V → V → V
_lookup_default_ {K} {V} k m v =
  lookup' (Map.pairs m)
    where
      _eq_ = Map.eqKey m
      lookup' : List (Pair K V) → V
      lookup' [] = v
      lookup' (pair k' v' ∷ xs) = if k eq k' then v' else lookup' xs

_delete_ : {K V : Set} → K → Map K V → Map K V
_delete_ {K} {V} k m =
  record m {pairs = delete' (Map.pairs m)}
    where
      _eq_ = Map.eqKey m
      delete' : List (Pair K V) → List (Pair K V)
      delete' [] = []
      delete' (x ∷ xs) = if k eq Pair.fst x then delete' xs else x ∷ delete' xs

_insert_into_ : {K V : Set} → K → V → Map K V → Map K V
_insert_into_ {K} {V} k v m =
  record m {pairs = record {fst = k; snd = v} ∷ delete' (Map.pairs m)}
    where
      _eq_ = Map.eqKey m
      delete' : List (Pair K V) → List (Pair K V)
      delete' [] = []
      delete' (x ∷ xs) = if k eq Pair.fst x then delete' xs else x ∷ delete' xs
