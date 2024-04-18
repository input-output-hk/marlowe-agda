{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Marlowe.Core.Contract where

import Control.Applicative ((<*>), (<|>))
import Data.Aeson as A (object, withArray, withObject, withText, withScientific, (.=), (.:), (.:?), encode)
import Data.Aeson.Types qualified as A (Parser, ToJSON(..), FromJSON(..), Value (..), prependFailure, typeMismatch)
import Data.Aeson.Encode.Pretty (encodePrettyToTextBuilder)
import qualified Data.Foldable as F
import Data.Scientific (Scientific (..), floatingOrInteger, scientific)
import Data.Text as T
import Data.Text.Lazy (toStrict)
import Data.Text.Lazy.Builder (toLazyText)

newtype PosixTime = PosixTime Integer
  deriving (Show, Eq)
newtype AccountId p = AccountId p
  deriving (Show, Eq, Ord)
newtype ChoiceName = ChoiceName Text
  deriving (Show, Eq, Ord)
data ChoiceId p = ChoiceId ChoiceName p
  deriving (Show, Eq, Ord)
newtype ValueId = ValueId Text
  deriving (Show, Eq, Ord)
newtype Timeout = Timeout PosixTime
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

data State p t = State
  { accounts :: [((AccountId p, t), Integer)],
    choices :: [(ChoiceId p, Integer)],
    boundValues :: [(ValueId, Integer)],
    minTime :: PosixTime
  }
  deriving (Show, Eq)

data TimeInterval = TimeInterval PosixTime Integer
  deriving (Show, Eq)

intervalEnd :: TimeInterval -> PosixTime
intervalEnd (TimeInterval (PosixTime i) d) = PosixTime (i + d)

data Environment = Environment TimeInterval
  deriving (Show, Eq)

data ChosenNum = ChosenNum Integer
  deriving (Show, Eq)

data Input p t
  = IDeposit (AccountId p) p t Integer
  | IChoice (ChoiceId p) ChosenNum
  | INotify
  deriving (Show, Eq)

data Payment p t = Payment (AccountId p) t Integer (Payee p)
  deriving (Show, Eq)

data TransactionWarning p t
  = TransactionNonPositiveDeposit p (AccountId p) t Integer
  | TransactionNonPositivePay (AccountId p) (Payee p) t Integer
  | TransactionPartialPay (AccountId p) (Payee p) t Integer Integer
  | TransactionShadowing ValueId Integer Integer
  | TransactionAssertionFailed
  deriving (Show, Eq)

data IntervalError
  = InvalidInterval TimeInterval
  | IntervalInPastError PosixTime TimeInterval
  deriving stock (Show, Eq)

data TransactionError
  = TEAmbiguousTimeIntervalError
  | TEApplyNoMatchError
  | TEIntervalError IntervalError
  | TEUselessTransaction
  | TEHashMismatch
  deriving (Show, Eq)

data TransactionOutput p t
  = TransactionOutput
      { txOutWarnings :: [TransactionWarning p t],
        txOutPayments :: [Payment p t],
        txOutState :: State p t,
        txOutContract :: Contract p t
      }
  | Error TransactionError
  deriving (Show, Eq)

showContract :: (Show p, Show t) => Contract p t -> Text
showContract = pack . show

showPayment :: (Show p, Show t) => Payment p t -> Text
showPayment = pack . show

-- JSON serialization

getInteger :: String -> Scientific -> A.Parser Integer
getInteger ctx x = case (floatingOrInteger x :: Either Double Integer) of
  Right a -> return a
  Left _ -> fail $ "parsing " ++ ctx ++ " failed, expected integer, but encountered floating point"

withInteger :: String -> A.Value -> A.Parser Integer
withInteger ctx = withScientific ctx $ getInteger ctx

instance A.ToJSON PosixTime where
  toJSON (PosixTime t) = A.toJSON t

instance A.FromJSON PosixTime where
  parseJSON i = PosixTime <$> withInteger "PosixTime" i

instance A.ToJSON ChoiceName where
  toJSON (ChoiceName s) = A.toJSON s

instance A.FromJSON ChoiceName where
  parseJSON = withText "ChoiceName" (pure . ChoiceName)

instance (A.ToJSON p) => A.ToJSON (ChoiceId p) where
  toJSON (ChoiceId name party) =
    object
      [ "choice_name" .= name,
        "choice_owner" .= party
      ]

instance (A.FromJSON p) => A.FromJSON (ChoiceId p) where
  parseJSON =
    withObject
      "ChoiceId"
      ( \v ->
          ChoiceId
            <$> (v .: "choice_name")
            <*> (v .: "choice_owner")
      )

instance (A.ToJSON p) => A.ToJSON (AccountId p) where
  toJSON (AccountId p) = A.toJSON p

instance (A.FromJSON p) => A.FromJSON (AccountId p) where
  parseJSON = A.parseJSON

instance A.ToJSON ValueId where
  toJSON (ValueId i) = A.toJSON i

instance A.FromJSON ValueId where
  parseJSON = withText "ValueId" (pure . ValueId)

instance (A.ToJSON p) => A.ToJSON (Payee p) where
  toJSON (Account account) =
    object ["account" .= account]
  toJSON (Party party) =
    object ["party" .= party]

instance (A.FromJSON p) => A.FromJSON (Payee p) where
  parseJSON = withObject "Payee" $
    \v -> asAccount v <|> asParty v
    where
      asAccount v = Account <$> v .: "account"
      asParty v = Party <$> v .: "party"

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (Observation p t) where
  toJSON (AndObs lhs rhs) =
    object
      [ "both" .= lhs,
        "and" .= rhs
      ]
  toJSON (OrObs lhs rhs) =
    object
      [ "either" .= lhs,
        "or" .= rhs
      ]
  toJSON (NotObs v) =
    object
      ["not" .= v]
  toJSON (ChoseSomething choiceId) =
    object
      ["chose_something_for" .= choiceId]
  toJSON (ValueGE lhs rhs) =
    object
      [ "value" .= lhs,
        "ge_than" .= rhs
      ]
  toJSON (ValueGT lhs rhs) =
    object
      [ "value" .= lhs,
        "gt" .= rhs
      ]
  toJSON (ValueLT lhs rhs) =
    object
      [ "value" .= lhs,
        "lt" .= rhs
      ]
  toJSON (ValueLE lhs rhs) =
    object
      [ "value" .= lhs,
        "le_than" .= rhs
      ]
  toJSON (ValueEQ lhs rhs) =
    object
      [ "value" .= lhs,
        "equal_to" .= rhs
      ]
  toJSON TrueObs = A.toJSON True
  toJSON FalseObs = A.toJSON False

instance A.ToJSON ChosenNum where
  toJSON (ChosenNum i) = A.toJSON i

instance A.FromJSON ChosenNum where
  parseJSON i = ChosenNum <$> withInteger "ChosenNum" i

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (Observation p t) where
  parseJSON (A.Bool True) = return TrueObs
  parseJSON (A.Bool False) = return FalseObs
  parseJSON (A.Object v) =
    ( AndObs
        <$> (v .: "both")
        <*> (v .: "and")
    )
      <|> ( OrObs
              <$> (v .: "either")
              <*> (v .: "or")
          )
      <|> (NotObs <$> (v .: "not"))
      <|> (ChoseSomething <$> (v .: "chose_something_for"))
      <|> ( ValueGE
              <$> (v .: "value")
              <*> (v .: "ge_than")
          )
      <|> ( ValueGT
              <$> (v .: "value")
              <*> (v .: "gt")
          )
      <|> ( ValueLT
              <$> (v .: "value")
              <*> (v .: "lt")
          )
      <|> ( ValueLE
              <$> (v .: "value")
              <*> (v .: "le_than")
          )
      <|> ( ValueEQ
              <$> (v .: "value")
              <*> (v .: "equal_to")
          )
  parseJSON _ = fail "Observation must be either an object or a boolean"

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (Value p t) where
  parseJSON (A.Object v) =
    ( AvailableMoney
        <$> (v .: "in_account")
        <*> (v .: "amount_of_token")
    )
      <|> (NegValue <$> (v .: "negate"))
      <|> ( AddValue
              <$> (v .: "add")
              <*> (v .: "and")
          )
      <|> ( SubValue
              <$> (v .: "value")
              <*> (v .: "minus")
          )
      <|> ( MulValue
              <$> (v .: "multiply")
              <*> (v .: "times")
          )
      <|> (DivValue <$> (v .: "divide") <*> (v .: "by"))
      <|> (ChoiceValue <$> (v .: "value_of_choice"))
      <|> (UseValue <$> (v .: "use_value"))
      <|> ( Cond
              <$> (v .: "if")
              <*> (v .: "then")
              <*> (v .: "else")
          )
  parseJSON (A.String "time_interval_start") = return TimeIntervalStart
  parseJSON (A.String "time_interval_end") = return TimeIntervalEnd
  parseJSON (A.Number n) = Constant <$> getInteger "constant value" n
  parseJSON _ = fail "Value must be either a string, object or an integer"

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (Value p t) where
  toJSON (AvailableMoney accountId token) =
    object
      [ "amount_of_token" .= token,
        "in_account" .= accountId
      ]
  toJSON (Constant x) = A.toJSON x
  toJSON (NegValue x) =
    object
      ["negate" .= x]
  toJSON (AddValue lhs rhs) =
    object
      [ "add" .= lhs,
        "and" .= rhs
      ]
  toJSON (SubValue lhs rhs) =
    object
      [ "value" .= lhs,
        "minus" .= rhs
      ]
  toJSON (MulValue lhs rhs) =
    object
      [ "multiply" .= lhs,
        "times" .= rhs
      ]
  toJSON (DivValue lhs rhs) =
    object
      [ "divide" .= lhs,
        "by" .= rhs
      ]
  toJSON (ChoiceValue choiceId) =
    object
      ["value_of_choice" .= choiceId]
  toJSON TimeIntervalStart = A.String $ T.pack "time_interval_start"
  toJSON TimeIntervalEnd = A.String $ T.pack "time_interval_end"
  toJSON (UseValue valueId) =
    object
      ["use_value" .= valueId]
  toJSON (Cond obs tv ev) =
    object
      [ "if" .= obs,
        "then" .= tv,
        "else" .= ev
      ]

instance A.ToJSON Bound where
  toJSON (Bound from to) =
    object
      [ "from" .= from,
        "to" .= to
      ]

instance A.FromJSON Bound where
  parseJSON =
    withObject
      "Bound"
      ( \v ->
          Bound
            <$> (getInteger "lower bound" =<< (v .: "from"))
            <*> (getInteger "higher bound" =<< (v .: "to"))
      )

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (Action p t) where
  toJSON (Deposit accountId party token val) =
    object
      [ "into_account" .= accountId,
        "party" .= party,
        "of_token" .= token,
        "deposits" .= val
      ]
  toJSON (Choice choiceId bounds) =
    object
      [ "for_choice" .= choiceId,
        "choose_between" .= A.toJSONList (Prelude.map A.toJSON bounds)
      ]
  toJSON (Notify obs) =
    object
      ["notify_if" .= obs]

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (Action p t) where
  parseJSON =
    withObject
      "Action"
      ( \v ->
          ( Deposit
              <$> (v .: "into_account")
              <*> (v .: "party")
              <*> (v .: "of_token")
              <*> (v .: "deposits")
          )
            <|> ( Choice
                    <$> (v .: "for_choice")
                    <*> ( (v .: "choose_between")
                            >>= withArray
                              "Bound list"
                              ( mapM A.parseJSON . F.toList
                              )
                        )
                )
            <|> (Notify <$> (v .: "notify_if"))
      )

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (Case p t) where
  toJSON (Case act cont) =
    object
      [ "case" .= act,
        "then" .= cont
      ]

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (Case p t) where
  parseJSON =
    withObject
      "Case"
      ( \v ->
          Case <$> (v .: "case") <*> (v .: "then")
      )

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (Contract p t) where
  parseJSON (A.String "close") = return Close
  parseJSON (A.Object v) =
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
                      >>= withArray "Case list" (mapM A.parseJSON . F.toList)
                  )
              <*> (Timeout . PosixTime <$> (withInteger "when timeout" =<< (v .: "timeout")))
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

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (Contract p t) where
  toJSON Close = A.String $ pack "close"
  toJSON (Pay accountId payee token value contract) =
    object
      [ "from_account" .= accountId,
        "to" .= payee,
        "token" .= token,
        "pay" .= value,
        "then" .= contract
      ]
  toJSON (If obs cont1 cont2) =
    object
      [ "if" .= obs,
        "then" .= cont1,
        "else" .= cont2
      ]
  toJSON (When caseList (Timeout timeout) cont) =
    object
      [ "when" .= A.toJSONList (Prelude.map A.toJSON caseList),
        "timeout" .= timeout,
        "timeout_continuation" .= cont
      ]
  toJSON (Let valId value cont) =
    object
      [ "let" .= valId,
        "be" .= value,
        "then" .= cont
      ]
  toJSON (Assert obs cont) =
    object
      [ "assert" .= obs,
        "then" .= cont
      ]

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (State p t) where
  parseJSON =
    withObject
      "State"
      ( \v ->
          State
            <$> (v .: "accounts" >>= A.parseJSON)
            <*> (v .: "choices" >>= A.parseJSON)
            <*> (v .: "boundValues" >>= A.parseJSON)
            <*> (PosixTime <$> (withInteger "minTime" =<< (v .: "minTime")))
      )
instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (State p t) where
  toJSON
    State
      { accounts = a
      , choices = c
      , boundValues = bv
      , minTime = PosixTime ms
      } =
      object
        [ "accounts" .= A.toJSON a
        , "choices" .= A.toJSON c
        , "boundValues" .= A.toJSON bv
        , "minTime" .= ms
        ]

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (Input p t) where
  parseJSON (A.String "input_notify") = return INotify
  parseJSON (A.Object v) =
    IChoice
      <$> v .: "for_choice_id"
      <*> v .: "input_that_chooses_num"
      <|> IDeposit
        <$> v .: "into_account"
        <*> v .: "input_from_party"
        <*> v .: "of_token"
        <*> v .: "that_deposits"
  parseJSON _ = fail "Input must be either an object or the string \"input_notify\""

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (Input p t) where
  toJSON (IDeposit accId party tok amount) =
    object
      [ "input_from_party" .= party,
        "that_deposits" .= amount,
        "of_token" .= tok,
        "into_account" .= accId
      ]
  toJSON (IChoice choiceId chosenNum) =
    object
      [ "input_that_chooses_num" .= chosenNum,
        "for_choice_id" .= choiceId
      ]
  toJSON INotify = A.String $ pack "input_notify"

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (Payment p t) where
  toJSON (Payment accountId payee token amount) =
    object
      [ "payment_from" .= accountId,
        "to" .= payee,
        "token" .= token,
        "amount" .= amount
      ]

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (Payment p t) where
  parseJSON =
    withObject "Payment" $
      \o ->
        Payment
          <$> o .: "payment_from"
          <*> o .: "to"
          <*> o .: "token"
          <*> o .: "amount"

posixTimeToJSON :: PosixTime -> A.Value
posixTimeToJSON (PosixTime n) = A.Number $ scientific n 0

instance A.ToJSON IntervalError where
  toJSON (InvalidInterval i@(TimeInterval s e)) =
    A.object
      [("invalidInterval", A.object [("from", posixTimeToJSON s), ("to", posixTimeToJSON $ intervalEnd i)])]
  toJSON (IntervalInPastError t i@(TimeInterval s e)) =
    A.object
      [ ( "intervalInPastError",
          A.object [("minTime", posixTimeToJSON t), ("from", posixTimeToJSON s), ("to", posixTimeToJSON $ intervalEnd i)]
        )
      ]

posixTimeFromJSON :: A.Value -> A.Parser PosixTime
posixTimeFromJSON = \case
  v@(A.Number n) ->
    either
      (\_ -> A.prependFailure "parsing PosixTime failed, " (A.typeMismatch "Integer" v))
      (return . PosixTime)
      (floatingOrInteger n :: Either Double Integer)
  invalid ->
    A.prependFailure "parsing PosixTime failed, " (A.typeMismatch "Number" invalid)

instance A.FromJSON IntervalError where
  parseJSON (A.Object v) =
    let parseInvalidInterval = do
          o <- v .: "invalidInterval"
          InvalidInterval <$> posixIntervalFromJSON o
        parseIntervalInPastError = do
          o <- v .: "intervalInPastError"
          IntervalInPastError
            <$> (posixTimeFromJSON =<< o .: "minTime")
            <*> posixIntervalFromJSON o
     in parseIntervalInPastError <|> parseInvalidInterval
    where
      posixIntervalFromJSON o = TimeInterval <$> (posixTimeFromJSON =<< o .: "from") <*> (o .: "to")
  parseJSON invalid =
    A.prependFailure "parsing IntervalError failed, " (A.typeMismatch "Object" invalid)

instance A.FromJSON TransactionError where
  parseJSON (A.String s) =
    case s of
      "TEAmbiguousTimeIntervalError" -> return TEAmbiguousTimeIntervalError
      "TEApplyNoMatchError" -> return TEApplyNoMatchError
      "TEUselessTransaction" -> return TEUselessTransaction
      "TEHashMismatch" -> return TEHashMismatch
      _ -> fail "Failed parsing TransactionError"
  parseJSON (A.Object o) = do
    err <- o .: "error"
    if err == ("TEIntervalError" :: String)
      then TEIntervalError <$> o .: "context"
      else fail "Failed parsing TransactionError"
  parseJSON _ = fail "Failed parsing TransactionError"

instance A.ToJSON TransactionError where
  toJSON TEAmbiguousTimeIntervalError = A.String "TEAmbiguousTimeIntervalError"
  toJSON TEApplyNoMatchError = A.String "TEApplyNoMatchError"
  toJSON (TEIntervalError intervalError) = object ["error" .= A.String "TEIntervalError", "context" .= intervalError]
  toJSON TEUselessTransaction = A.String "TEUselessTransaction"
  toJSON TEHashMismatch = A.String "TEHashMismatch"

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (TransactionWarning p t) where
  parseJSON (A.String "assertion_failed") = return TransactionAssertionFailed
  parseJSON (A.Object v) =
    ( TransactionNonPositiveDeposit
        <$> (v .: "party")
        <*> (v .: "in_account")
        <*> (v .: "of_token")
        <*> (v .: "asked_to_deposit")
    )
      <|> ( do
              maybeButOnlyPaid <- v .:? "but_only_paid"
              case maybeButOnlyPaid :: Maybe Scientific of
                Nothing ->
                  TransactionNonPositivePay
                    <$> (v .: "account")
                    <*> (v .: "to_payee")
                    <*> (v .: "of_token")
                    <*> (v .: "asked_to_pay")
                Just butOnlyPaid ->
                  TransactionPartialPay
                    <$> (v .: "account")
                    <*> (v .: "to_payee")
                    <*> (v .: "of_token")
                    <*> getInteger "but only paid" butOnlyPaid
                    <*> (v .: "asked_to_pay")
          )
      <|> ( TransactionShadowing
              <$> (v .: "value_id")
              <*> (v .: "had_value")
              <*> (v .: "is_now_assigned")
          )
  parseJSON _ = fail "Contract must be either an object or a the string \"close\""

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (TransactionWarning p t) where
  toJSON (TransactionNonPositiveDeposit party accId tok amount) =
    object
      [ "party" .= party,
        "asked_to_deposit" .= amount,
        "of_token" .= tok,
        "in_account" .= accId
      ]
  toJSON (TransactionNonPositivePay accId payee tok amount) =
    object
      [ "account" .= accId,
        "asked_to_pay" .= amount,
        "of_token" .= tok,
        "to_payee" .= payee
      ]
  toJSON (TransactionPartialPay accId payee tok paid expected) =
    object
      [ "account" .= accId,
        "asked_to_pay" .= expected,
        "of_token" .= tok,
        "to_payee" .= payee,
        "but_only_paid" .= paid
      ]
  toJSON (TransactionShadowing valId oldVal newVal) =
    object
      [ "value_id" .= valId,
        "had_value" .= oldVal,
        "is_now_assigned" .= newVal
      ]
  toJSON TransactionAssertionFailed = A.String $ pack "assertion_failed"

instance (A.ToJSON p, A.ToJSON t) => A.ToJSON (TransactionOutput p t) where
  toJSON TransactionOutput {..} =
    object
      [ "warnings" .= txOutWarnings,
        "payments" .= txOutPayments,
        "state" .= txOutState,
        "contract" .= txOutContract
      ]
  toJSON (Error err) = object ["transaction_error" .= err]

instance (A.FromJSON p, A.FromJSON t) => A.FromJSON (TransactionOutput p t) where
  parseJSON =
    withObject "TransactionOutput" $
      \o ->
        let asTransactionOutput =
              TransactionOutput
                <$> o .: "warnings"
                <*> o .: "payments"
                <*> o .: "state"
                <*> o .: "contract"
            asError = Error <$> o .: "transaction_error"
         in asTransactionOutput <|> asError

-- Cardano specific types

data Token = Token Text Text
  deriving (Show, Eq, Ord)

instance A.ToJSON Token where
  toJSON (Token currSym tokName) =
    object
      [ "currency_symbol" .= currSym,
        "token_name" .= tokName
      ]

instance A.FromJSON Token where
  parseJSON =
    withObject
      "Token"
      ( \v ->
          Token
            <$> (v .: "currency_symbol")
            <*> (v .: "token_name")
      )

data Party
  = Address Text
  | Role Text
  deriving (Show, Eq, Ord)

instance A.ToJSON Party where
  toJSON (Address address) =
    object ["address" .= address]
  toJSON (Role name) =
    object ["role_token" .= name]

instance A.FromJSON Party where
  parseJSON = withObject "Party" $
    \v -> asAddress v <|> asRole v
    where
      asAddress v = Address <$> v .: "address"
      asRole v = Role <$> v .: "role_token"

contractJSON :: A.ToJSON p => A.ToJSON t => Contract p t -> Text
contractJSON = toStrict . toLazyText . encodePrettyToTextBuilder
