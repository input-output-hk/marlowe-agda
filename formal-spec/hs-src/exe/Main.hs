module Main where

import Lib

main :: IO ()
main =
  let (posixTime, (contract, inputs)) = escrowExample
   in print $ evalBs contract (MkState [] [] [] posixTime) inputs
