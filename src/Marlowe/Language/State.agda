
module Marlowe.Language.State where


open import Agda.Builtin.Int using (Int)
open import Marlowe.Language.Contract using (AccountId; ChoiceId; Token; ValueId)
open import Primitives using (Map; Pair; PosixTime)


Accounts : Set
Accounts = Map (Pair AccountId Token) Int


record State : Set where
  field
    accounts : Accounts
    choices : Map ChoiceId Int
    boundValues : Map ValueId Int
    minTime : PosixTime


TimeInterval : Set
TimeInterval = Pair PosixTime PosixTime


record Environment : Set where
  field
    timeInterval : TimeInterval
