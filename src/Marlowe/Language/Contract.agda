

module Marlowe.Language.Contract where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Primitives using (ByteString; PosixTime)


data Party : Set where
  Address : ByteString → Party
  Role : ByteString → Party


data AccountId : Set where
  mkAccountId : Party → AccountId


data Timeout : Set where
  mkTimeout : PosixTime → Timeout


data ChoiceName : Set where
  mkChoiceName : ByteString → ChoiceName


data ChoiceId : Set where
  mkChoiceId : ChoiceName → Party → ChoiceId


data Token : Set where
  mkToken : ByteString → Token
  

data ValueId : Set where
  mkValueId : ByteString → ValueId


data Observation : Set

data Value : Set where
  AvailableMoney : AccountId → Token → Value
  Constant : Int → Value
  NegValue : Value → Value
  AddValue : Value → Value → Value
  SubValue : Value → Value → Value
  MulValue : Value → Value → Value
  DivValue : Value → Value → Value
  ChoiceValue : ChoiceId → Value
  TimeIntervalStart : Value
  TimeIntervalEnd : Value
  UseValue : ValueId → Value
  Cond : Observation → Value → Value → Value

data Observation where
  AndObs : Observation → Observation → Observation
  OrObs : Observation → Observation → Observation
  NotObs : Observation → Observation
  ChoseSomething : ChoiceId → Observation
  ValueGE : Value → Value → Observation
  ValueGT : Value → Value → Observation
  ValueLT : Value → Value → Observation
  ValueLE : Value → Value → Observation
  ValueEQ : Value → Value → Observation
  TrueObs : Observation
  FalseObs : Observation


data Bound : Set where
  mkBound : Int → Int → Bound


data Action : Set where
  Deposit : AccountId → Party → Token → Value → Action
  Choice : ChoiceId → List Bound → Action
  Notify : Observation → Action


data Payee : Set where
  mkAccount : AccountId → Payee
  mkParty : Party → Payee
  

data Contract : Set

data Case : Set where
  mkCase : Action → Contract → Case

data Contract where
  Close : Contract
  Pay : AccountId → Payee → Token → Value → Contract → Contract
  If : Observation → Contract → Contract → Contract
  When : List Case → Timeout → Contract → Contract
  Let : ValueId → Value → Contract → Contract
  Assert : Observation → Contract → Contract


