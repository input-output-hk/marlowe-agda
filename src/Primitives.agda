

module Primitives where


open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)


data ByteString : Set where
  mkByteString : String → ByteString


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

_member_ : {K V : Set} → K → Map K V → Bool
_member_ _ _ = false  -- FIXME

_lookup_default_ : {K V : Set} → K → Map K V → V → V
_lookup_default_ _ _ v = v  -- FIXME
