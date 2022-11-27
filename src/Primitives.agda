

module Primitives where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)


data ByteString : Set where
  mkByteString : String → ByteString


data PosixTime : Set where
  mkPosixTime : Int → PosixTime


record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B


data Map (K V : Set) : Set where
  mkMap : List (Pair K V) → Map K V
