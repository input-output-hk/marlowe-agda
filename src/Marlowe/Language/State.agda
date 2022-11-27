

module Marlowe.Language.State where


open import Agda.Builtin.Int using (Int)
open import Marlowe.Language.Contract using (AccountId; ChoiceId; Token; ValueId)
open import Primitives using (Map; Pair; PosixTime)


data Accounts : Set where
  mkAccounts : Map (Pair AccountId Token) Int → Accounts


record State : Set where
  field
    accounts : Accounts
    choices : Map ChoiceId Int
    boundValues : Map ValueId Int
    minTime : PosixTime


data TimeInterval : Set where
  mkTimeInterval : Pair PosixTime PosixTime → TimeInterval

unTimeInterval : TimeInterval → Pair PosixTime PosixTime
unTimeInterval (mkTimeInterval i) = i


record Environment : Set where
  field
    timeInterval : TimeInterval
