

{-# OPTIONS --guardedness #-}


module main where


open import Data.List.Base using ([]; _∷_)
open import IO
open import Marlowe.Language.Contract
open import Marlowe.Serialization.Json
open import Marlowe.Examples.Escrow
open import Marlowe.Semantics.Operate
open import Primitives

open Json {{...}} public


pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []


main : Main
main =
  let
    triple minTime contract inputs = escrowExample
    output = playTrace minTime contract inputs
  in
    run
      (
        putStrLn
          (
            object
              [
                "minTime" kv minTime
              , "contract" kv contract
              , "inputs" kv inputs
              , "output" kv output
              ]
          )
      )
