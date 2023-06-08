

module Marlowe.Serialization.Json where

open import Agda.Builtin.String using (primShowString)
open import Agda.Builtin.Int using (Int)
open import Data.Integer.Show using (show)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String
open import Data.String.Base using (intersperse)
open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Primitives
open import Data.List.Base using (List; map; []; _∷_)


JSON : Set
JSON = String


record Json a : Set where
  field
    toJson : a → JSON

open Json {{...}} public


_kv_ : ∀ {a : Set} → {{_ : Json a}} → String → a → String × JSON
_kv_ k v = ⟨ k , toJson v ⟩


object : List (String × JSON) → JSON
object pairs =
  "{" ++ intersperse "," (map render pairs) ++ "}"
    where
      render : String × JSON → String
      render ⟨ k , v ⟩ = primShowString k ++ ":" ++ v


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []


instance
  IntJson : Json Int
  toJson {{IntJson}} = Data.Integer.Show.show


instance
  StringJson : Json String
  toJson {{StringJson}} = primShowString


instance
  PairJson : ∀ {K V : Set} → {{_ : Json K}} → {{_ : Json V}} → Json (K × V)
  toJson {{PairJson}} ⟨ k , v ⟩ = "[" ++ toJson k ++ "," ++ toJson v ++ "]"


instance
  ListJson : ∀ {a : Set} → {{_ : Json a}} → Json (List a)
  toJson {{ListJson}} xs = "[" ++ intersperse "," (map toJson xs) ++ "]"


instance
  MapJson : ∀ {K V : Set} → {{_ : Json K}} → {{_ : Json V}} → Json (Map K V)
  toJson {{MapJson}} m = toJson (Map.pairs m)


instance
  ByteStringJson : Json ByteString
  toJson {{ByteStringJson}} (mkByteString s) = toJson s
  

instance
  PosixTimeJson : Json PosixTime
  toJson {{PosixTimeJson}} (mkPosixTime t) = toJson t


instance
  PartyJson : Json Party
  toJson {{PartyJson}} (Address address) = object [("address" kv address)]
  toJson {{PartyJson}} (Role role) = object [("role_token" kv role)]


instance
  AccountIdJson : Json AccountId
  toJson {{AccountIdJson}} (mkAccountId party) = toJson party


instance
  TimeoutJson : Json Timeout
  toJson {{TimeoutJson}} (mkTimeout t) = toJson t


instance
  ChoiceNameJson : Json ChoiceName
  toJson {{ChoiceNameJson}} (mkChoiceName s) = toJson s


instance
  ChoiceIdJson : Json ChoiceId
  toJson {{ChoiceIdJson}} (mkChoiceId name owner) =
    object
      [
        "choice_name" kv name
      , "choice_owner" kv owner
      ]

instance
  TokenJson : Json Token
  toJson {{TokenJson}} (mkToken symbol name) =
    object
      [
        "currency_symbol" kv symbol
      , "token_name" kv name
      ]


instance
  ValueIdJson : Json ValueId
  toJson {{ValueIdJson}} (mkValueId value) = toJson value


instance
  {-# TERMINATING #-}
  ObservationJson : Json Observation
  {-# TERMINATING #-}
  ValueJson : Json Value
  toJson {{ValueJson}} (AvailableMoney account token) = object [("amount_of_token" kv token), ("in_account" kv account)]
  toJson {{ValueJson}} (Constant x) = Data.Integer.Show.show x
  toJson {{ValueJson}} (NegValue x) = object [("negate" kv x)]
  toJson {{ValueJson}} (AddValue x y) = object [("add" kv x), ("and" kv y)]
  toJson {{ValueJson}} (SubValue x y) = object [("value" kv x), ("minus" kv y)]
  toJson {{ValueJson}} (MulValue x y) = object [("multiply" kv x), ("times" kv y)]
  toJson {{ValueJson}} (DivValue x y) = object [("divide" kv x), ("by" kv y)]
  toJson {{ValueJson}} (ChoiceValue choice) = object [("value_of_choice" kv choice)]
  toJson {{ValueJson}} TimeIntervalStart = toJson "time_interval_start"
  toJson {{ValueJson}} TimeIntervalEnd = toJson "time_interval_end"
  toJson {{ValueJson}} (UseValue value) = object [("use_value" kv value)]
  toJson {{ValueJson}} (Cond o x y) = object [("if" kv o), ("then" kv x), ("else" kv y)]
  toJson {{ObservationJson}} (AndObs x y) = object [("both" kv x), ("and" kv y)]
  toJson {{ObservationJson}} (OrObs x y) = object [("either" kv x), ("or" kv y)]
  toJson {{ObservationJson}} (NotObs x) = object [("not" kv x)]
  toJson {{ObservationJson}} (ChoseSomething choice) = object [("chose_something_for" kv choice)]
  toJson {{ObservationJson}} (ValueGE x y) = object [("value" kv x), ("ge_than" kv y)]
  toJson {{ObservationJson}} (ValueGT x y) = object [("value" kv x), ("gt" kv y)]
  toJson {{ObservationJson}} (ValueLT x y) = object [("value" kv x), ("lt" kv y)]
  toJson {{ObservationJson}} (ValueLE x y) = object [("value" kv x), ("le_than" kv y)]
  toJson {{ObservationJson}} (ValueEQ x y) = object [("value" kv x), ("equal_to" kv y)]
  toJson {{ObservationJson}} TrueObs = "true"
  toJson {{ObservationJson}} FalseObs = "false"


instance
  BoundJson : Json Bound
  toJson {{BoundJson}} (mkBound from to) = object [("from" kv from), ("to" kv to)]


instance
  ActionJson : Json Action
  toJson {{ActionJson}} (Deposit account party token value) =
    object
      [
        "into_account" kv account
      , "party" kv party
      , "of_token" kv token
      , "deposits" kv value
      ]
  toJson {{ActionJson}} (Choice choice bounds) =
    object
      [
        "for_choice" kv choice
      , "choose_between" kv bounds
      ]
  toJson {{ActionJson}} (Notify o) =
    object
      [
        "notify_if" kv o
      ]


instance
  PayeeJson : Json Payee
  toJson {{PayeeJson}} (mkAccount account) = object [("account" kv account)]
  toJson {{PayeeJson}} (mkParty party) = object [("party" kv party)]
  

instance
  {-# TERMINATING #-}
  CaseJson : Json Case
  {-# TERMINATING #-}
  ContractJson : Json Contract
  toJson {{CaseJson}} (mkCase action contract) =
    object
      [
        "case" kv action
      , "then" kv contract
      ]
  toJson {{ContractJson}} Close =
    toJson "close"
  toJson {{ContractJson}} (Pay account payee token value contract) =
    object
      [
        "from_account" kv account
      , "to" kv payee
      , "token" kv token
      , "pay" kv value
      , "then" kv contract
      ]
  toJson {{ContractJson}} (If observation thenContract elseContract) =
    object
      [
        "if" kv observation
      , "then" kv thenContract
      , "else" kv elseContract
      ]
  toJson {{ContractJson}} (When cases timeout contract) =
    object
      [
        "when" kv cases
      , "timeout" kv timeout
      , "timeout_continuation" kv contract
      ]
  toJson {{ContractJson}} (Let name value contract) =
    object
      [
        "let" kv name
      , "be" kv value
      , "then" kv contract
      ]
  toJson {{ContractJson}} (Assert observation contract) =
    object
      [
        "assert" kv observation
      , "then" kv contract
      ]


instance
  StateJson : Json State
  toJson {{StateJson}} (mkState accounts choices boundValues minTime) =
    object
      [
        "accounts" kv accounts
      , "choices" kv choices
      , "boundValues" kv boundValues
      , "minTime" kv minTime
      ]

instance
  EnvironmentJson : Json Environment
  toJson {{EnvironmentJson}} (mkEnvironment ⟨ x , y ⟩ ) =
    object
      [
        "from" kv x
      , "to" kv y
      ]


instance
  ChosenNumJson : Json ChosenNum
  toJson {{ChosenNumJson}} (mkChosenNum i) = toJson i


instance
  InputContentJson : Json InputContent
  toJson {{InputContentJson}} (IDeposit account party token amount) =
    object
      [
        "input_from_party" kv party
      , "that_deposits" kv amount
      , "of_token" kv token
      , "into_account" kv account
      ]
  toJson {{InputContentJson}} (IChoice choice number) =
    object
      [
        "input_that_chooses_num" kv number
      , "for_choice_id" kv choice
      ]
  toJson {{InputContentJson}} INotify =
    toJson "input_notify"


instance
  InputJson : Json Input
  toJson {{InputJson}} (NormalInput input) = toJson input


instance
  IntervalErrorJson : Json IntervalError
  toJson {{IntervalErrorJson}} (InvalidInterval ⟨ x , y ⟩ ) =
    object
      [
        ⟨ "invalidInterval" ,
          (
            object
              [
                "from" kv x
              , "to" kv y
              ]
          )
        ⟩
      ]
  toJson {{IntervalErrorJson}} (IntervalInPastError t ⟨ x , y ⟩ ) =
    object
      [
        ⟨ "intervalInPastError" ,
          (
            object
              [
                "minTime" kv t
              , "from" kv x
              , "to" kv y
              ]
          )
        ⟩
      ]


instance
  PaymentJson : Json Payment
  toJson {{PaymentJson}} (mkPayment account payee token amount) =
    object
      [
        "payment_from" kv account
      , "to" kv payee
      , "token" kv token
      , "amount" kv amount
      ]


instance
  TransactionWarningJson : Json TransactionWarning
  toJson {{TransactionWarningJson}} (TransactionNonPositiveDeposit party account token amount) =
    object
      [
        "party" kv party
      , "asked_to_deposit" kv amount
      , "of_token" kv token
      , "in_account" kv account
      ]
  toJson {{TransactionWarningJson}} (TransactionNonPositivePay account payee token amount) =
    object
      [
        "account" kv account
      , "asked_to_pay" kv amount
      , "of_token" kv token
      , "to_payee" kv payee
      ]
  toJson {{TransactionWarningJson}} (TransactionPartialPay account payee token paid expected) =
    object
      [
        "account" kv account
      , "asked_to_pay" kv expected
      , "of_token" kv token
      , "to_payee" kv payee
      , "but_only_paid" kv paid
      ]
  toJson {{TransactionWarningJson}} (TransactionShadowing value old new) =
    object
      [
        "value_id" kv value
      , "had_value" kv old
      , "is_now_assigned" kv new
      ]
  toJson {{TransactionWarningJson}} TransactionAssertionFailed = toJson "assertion_failed"


instance
  TransactionErrorJson : Json TransactionError
  toJson {{TransactionErrorJson}} TEAmbiguousTimeIntervalError = toJson "TEAmbiguousTimeIntervalError"
  toJson {{TransactionErrorJson}} TEApplyNoMatchError = toJson "TEApplyNoMatchError"
  toJson {{TransactionErrorJson}} (TEIntervalError context) =
    object
      [
        "error" kv "TEIntervalError"
      , "context" kv context
      ]
  toJson {{TransactionErrorJson}} TEUselessTransaction = toJson "TEUselessTransaction"
  toJson {{TransactionErrorJson}} TEHashMismatch = toJson "TEHashMismatch"


instance
  TransactionInputJson : Json TransactionInput
  toJson {{TransactionInputJson}} (mkTransactionInput ⟨ x , y ⟩ inputs) =
    object
      [
        ⟨ "tx_interval" ,
          (
            object
              [
                "from" kv x
              , "to" kv y
              ]
          )
        ⟩
      , "tx_inputs" kv inputs
      ]


instance
  TransactionOutputJson : Json TransactionOutput
  toJson {{TransactionOutputJson}} (mkTransactionOutput warnings payments state contract) =
    object
      [
        "warnings" kv warnings
      , "payments" kv payments
      , "state" kv state
      , "contract" kv contract
      ]
  toJson {{TransactionOutputJson}} (mkError error) =
    object
      [
        "transaction_error" kv error
      ]
