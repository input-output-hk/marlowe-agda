{-# LANGUAGE FlexibleInstances #-}

module Marlowe.Core.Contract where

import Data.Text

data PosixTime = PosixTime Integer
  deriving (Show, Eq)
data Party = Address Text
           | Role Text
  deriving (Show, Eq)
data AccountId p = AccountId p
  deriving (Show, Eq)
data ChoiceName = ChoiceName Text
  deriving (Show, Eq)
data ChoiceId p = ChoiceId ChoiceName p
  deriving (Show, Eq)
data ValueId = ValueId Text
  deriving (Show, Eq)
data Token = Token Text Text
  deriving (Show, Eq)
data Timeout = Timeout PosixTime
  deriving (Show, Eq)

data Observation p t = AndObs (Observation p t) (Observation p t)
                 | OrObs (Observation p t) (Observation p t)
                 | NotObs (Observation p t)
                 | ChoseSomething (ChoiceId p)
                 | ValueGE (Value p t) (Value p t)
                 | ValueGT (Value p t) (Value p t)
                 | ValueLT (Value p t) (Value p t)
                 | ValueLE (Value p t) (Value p t)
                 | ValueEQ (Value p t) (Value p t)
                 | TrueObs
                 | FalseObs
  deriving (Show, Eq)

data Value p t = AvailableMoney (AccountId p) t
           | Constant Integer
           | NegValue (Value p t)
           | AddValue (Value p t) (Value p t)
           | SubValue (Value p t) (Value p t)
           | MulValue (Value p t) (Value p t)
           | DivValue (Value p t) (Value p t)
           | ChoiceValue (ChoiceId p)
           | TimeIntervalStart
           | TimeIntervalEnd
           | UseValue ValueId
           | Cond (Observation p t) (Value p t) (Value p t)
  deriving (Show, Eq)

data Bound = Bound Integer Integer
  deriving (Show, Eq)

data Action p t = Deposit (AccountId p) p t (Value p t)
            | Choice (ChoiceId p) [Bound]
            | Notify (Observation p t)
  deriving (Show, Eq)

data Payee p = Account (AccountId p)
           | Party p
  deriving (Show, Eq)

data Contract p t = Close
              | Pay (AccountId p) (Payee p) t (Value p t) (Contract p t)
              | If (Observation p t) (Contract p t) (Contract p t)
              | When [Case p t] Timeout (Contract p t)
              | Let ValueId (Value p t) (Contract p t)
              | Assert (Observation p t) (Contract p t)
  deriving (Show, Eq)

data Case p t = Case (Action p t) (Contract p t)
  deriving (Show, Eq)

printContract :: (Show p, Show t) => Contract p t -> Text
printContract = pack . show
