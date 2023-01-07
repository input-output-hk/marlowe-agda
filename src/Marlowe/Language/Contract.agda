
module Marlowe.Language.Contract where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Data.Bool using (Bool; false; _∧_)
open import Primitives
open import Relation.Nullary.Decidable using (⌊_⌋)


data Party : Set where
  Address : ByteString → Party
  Role : ByteString → Party

_eqParty_ : Party → Party → Bool
_eqParty_ (Address x) (Address y) = x eqByteString y
_eqParty_ (Role x) (Role y) = x eqByteString y
_eqParty_ _ _ = false


data AccountId : Set where
  mkAccountId : Party → AccountId

_eqAccountId_ : AccountId → AccountId → Bool
_eqAccountId_ (mkAccountId x) (mkAccountId y) = x eqParty y


data Timeout : Set where
  mkTimeout : PosixTime → Timeout


data ChoiceName : Set where
  mkChoiceName : ByteString → ChoiceName

_eqChoiceName_ : ChoiceName → ChoiceName → Bool
_eqChoiceName_ (mkChoiceName x) (mkChoiceName y) = x eqByteString y


data ChoiceId : Set where
  mkChoiceId : ChoiceName → Party → ChoiceId

_eqChoiceId_ : ChoiceId → ChoiceId → Bool
_eqChoiceId_ (mkChoiceId xn xp) (mkChoiceId yn yp) = (xn eqChoiceName yn) ∧ (xp eqParty yp)


data Token : Set where
  mkToken : ByteString → Token

_eqToken_ : Token → Token → Bool
_eqToken_ (mkToken x) (mkToken y) = x eqByteString y
    

data ValueId : Set where
  mkValueId : ByteString → ValueId

_eqValueId_ : ValueId → ValueId → Bool
_eqValueId_ (mkValueId x) (mkValueId y) = x eqByteString y


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


getAction : Case → Action
getAction (mkCase action _) = action


data Contract where
  Close : Contract
  Pay : AccountId → Payee → Token → Value → Contract → Contract
  If : Observation → Contract → Contract → Contract
  When : List Case → Timeout → Contract → Contract
  Let : ValueId → Value → Contract → Contract
  Assert : Observation → Contract → Contract
