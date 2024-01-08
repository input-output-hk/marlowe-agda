{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Core.Contract where

import Data.Text
-- import qualified Data.Aeson as JSON
-- import qualified Data.Aeson.Types as JSON

data PosixTime = PosixTime Integer
  deriving (Show, Eq)
data Party = Address Text
           | Role Text
  deriving (Show, Eq)

data AccountId p t = AccountId p
  deriving (Show, Eq)
data ChoiceName = ChoiceName Text
  deriving (Show, Eq)
data ChoiceId p t = ChoiceId ChoiceName p
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
                 | ChoseSomething (ChoiceId p t)
                 | ValueGE (Value p t) (Value p t)
                 | ValueGT (Value p t) (Value p t)
                 | ValueLT (Value p t) (Value p t)
                 | ValueLE (Value p t) (Value p t)
                 | ValueEQ (Value p t) (Value p t)
                 | TrueObs
                 | FalseObs
  deriving (Show, Eq)

data Value p t = AvailableMoney (AccountId p t) t
           | Constant Integer
           | NegValue (Value p t)
           | AddValue (Value p t) (Value p t)
           | SubValue (Value p t) (Value p t)
           | MulValue (Value p t) (Value p t)
           | DivValue (Value p t) (Value p t)
           | ChoiceValue (ChoiceId p t)
           | TimeIntervalStart
           | TimeIntervalEnd
           | UseValue ValueId
           | Cond (Observation p t) (Value p t) (Value p t)
  deriving (Show, Eq)

data Bound = Bound Integer Integer
  deriving (Show, Eq)

data Action p t = Deposit (AccountId p t) p t (Value p t)
            | Choice (ChoiceId p t) [Bound]
            | Notify (Observation p t)
  deriving (Show, Eq)

data Payee p t = Account (AccountId p t)
           | Party p
  deriving (Show, Eq)

data Contract p t = Close
              | Pay (AccountId p t) (Payee p t) t (Value p t) (Contract p t)
              | If (Observation p t) (Contract p t) (Contract p t)
              | When [Case p t] Timeout (Contract p t)
              | Let ValueId (Value p t) (Contract p t)
              | Assert (Observation p t) (Contract p t)
  deriving (Show, Eq)

data Case p t = Case (Action p t) (Contract p t)
  deriving (Show, Eq)

    {-
instance JSON.ToJSON Contract where
   toJSON Close = JSON.String $ pack "close"
   toJSON _ = JSON.String $ pack "not-close"

instance JSON.FromJSON Contract where
  parseJSON (JSON.String "close") = return Close
  parseJSON (Object v) =
    ( Pay
        <$> (v .: "from_account")
        <*> (v .: "to")
        <*> (v .: "token")
        <*> (v .: "pay")
        <*> (v .: "then")
    )
      <|> ( If
              <$> (v .: "if")
              <*> (v .: "then")
              <*> (v .: "else")
          )
      <|> ( When
              <$> ( (v .: "when")
                      >>= withArray
                        "Case list"
                        ( \cl ->
                            mapM parseJSON (F.toList cl)
                        )
                  )
              <*> (POSIXTime <$> (withInteger "when timeout" =<< (v .: "timeout")))
              <*> (v .: "timeout_continuation")
          )
      <|> ( Let
              <$> (v .: "let")
              <*> (v .: "be")
              <*> (v .: "then")
          )
      <|> ( Assert
              <$> (v .: "assert")
              <*> (v .: "then")
          )
  parseJSON _ = fail "Contract must be either an object or a the string \"close\""
          -}

