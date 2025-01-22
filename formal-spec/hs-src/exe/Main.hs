module Main where

import Lib

val :: Value
val = AddValue (Constant 1) (Constant 7)

st :: State
st = undefined

env :: Environment
env = undefined

main :: IO ()
main =
  let v = evalValue env st val
   in putStrLn $ show v

