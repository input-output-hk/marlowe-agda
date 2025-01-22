module Main where

import Lib

main :: IO ()
main =
  let (a,(b,c)) = escrowExample
   in print $ evalBs b (MkState [] [] [] a) c
