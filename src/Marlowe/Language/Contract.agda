{-# OPTIONS --sized-types #-}

module Marlowe.Language.Contract where

open import Agda.Builtin.Size
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Data.Bool using (Bool; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Nat as ℕ using (ℕ; _⊔_)
open import Data.Product using (_×_; _,_)
open import Data.Product.Properties using (≡-dec)
open import Data.String as String using (String)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; _≡_; _≢_)
open import Relation.Nullary using (yes; no)

data ByteString : Set where
  mkByteString : String → ByteString

unByteString : ByteString → String
unByteString (mkByteString s) = s

_≟-ByteString_ : DecidableEquality ByteString
mkByteString s₁ ≟-ByteString mkByteString s₂ with s₁ String.≟ s₂
... | yes p = yes (cong mkByteString p)
... | no ¬p = no λ x → ¬p (cong unByteString x)

record PosixTime : Set where
  constructor mkPosixTime
  field
    getPosixTime : ℕ

data Party : Set where
  Address : ByteString → Party
  Role : ByteString → Party

unParty : Party → ByteString
unParty (Address x) = x
unParty (Role x) = x

_≟-Party_ : DecidableEquality Party
Address b₁ ≟-Party Address b₂ with b₁ ≟-ByteString b₂
... | yes p = yes (cong Address p)
... | no ¬p = no λ x → let y = cong unParty x in ¬p y
Role b₁ ≟-Party Role b₂ with b₁ ≟-ByteString b₂
... | yes p = yes (cong Role p)
... | no ¬p = no λ x → let y = cong unParty x in ¬p y
Role _ ≟-Party Address _ = no λ ()
Address _ ≟-Party Role _ = no λ ()

data AccountId : Set where
  mkAccountId : Party → AccountId

unAccountId : AccountId → Party
unAccountId (mkAccountId a) = a

_≟-AccountId_ : DecidableEquality AccountId
mkAccountId a₁ ≟-AccountId mkAccountId a₂ with a₁ ≟-Party a₂
... | yes p = yes (cong mkAccountId p)
... | no ¬p = no λ x → ¬p (cong unAccountId x)

data Timeout : Set where
  mkTimeout : PosixTime → Timeout

data ChoiceName : Set where
  mkChoiceName : ByteString → ChoiceName

unChoiceName : ChoiceName → ByteString
unChoiceName (mkChoiceName s) = s

_≟-ChoiceName_ : DecidableEquality ChoiceName
mkChoiceName b₁ ≟-ChoiceName mkChoiceName b₂ with b₁ ≟-ByteString b₂
... | yes p = yes (cong mkChoiceName p)
... | no ¬p = no λ x → ¬p (cong unChoiceName x)

record ChoiceId : Set where
  constructor mkChoiceId
  field
    name : ChoiceName
    party : Party

_≟-ChoiceId_ : DecidableEquality ChoiceId
mkChoiceId n₁ p₁ ≟-ChoiceId mkChoiceId n₂ p₂ with n₁ ≟-ChoiceName n₂ | p₁ ≟-Party p₂
... | yes p | yes q = yes (cong₂ mkChoiceId p q)
... | _ | no ¬q = no λ x → ¬q (cong ChoiceId.party x)
... | no ¬p | _ = no λ x → ¬p (cong ChoiceId.name x)

data Token : Set where
  mkToken : ByteString → ByteString → Token

getCurrencySymbol : Token → ByteString
getCurrencySymbol (mkToken c _) = c

getTokenName : Token → ByteString
getTokenName (mkToken _ n) = n

_≟-Token_ : DecidableEquality Token
mkToken c₁ n₁ ≟-Token mkToken c₂ n₂ with c₁ ≟-ByteString c₂ | n₁ ≟-ByteString n₂
... | yes p | yes q = yes (cong₂ mkToken p q)
... | _ | no ¬q = no λ x → ¬q (cong getTokenName x)
... | no ¬p | _ = no λ x → ¬p (cong getCurrencySymbol x)

record ValueId : Set where
  constructor mkValueId
  field
    getValueId : ByteString

_≟-ValueId_ : DecidableEquality ValueId
mkValueId b₁ ≟-ValueId mkValueId b₂ with b₁ ≟-ByteString b₂
... | yes p = yes (cong mkValueId p)
... | no ¬p = no λ x → ¬p (cong getValueId x) where open ValueId

_≟-AccountId×Token_ : DecidableEquality (AccountId × Token)
_≟-AccountId×Token_ = let _eq_ = ≡-dec _≟-AccountId_ _≟-Token_ in λ x y → x eq y

_≟-Party×Token_ : DecidableEquality (Party × Token)
_≟-Party×Token_ = let _eq_ = ≡-dec _≟-Party_ _≟-Token_ in λ x y → x eq y

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


data Contract : {i : Size} → Set

data Case : {i : Size} → Set where
  mkCase : {i : Size} → Action → Contract {i} → Case

data Contract where
  Close : {i : Size} → Contract {i}
  Pay : {i : Size} → AccountId → Payee → Token → Value → Contract {i} → Contract {↑ i}
  If : {i : Size} → Observation → Contract {i} → Contract {i} → Contract {↑ i}
  When : {i : Size} → List (Case {i}) → Timeout → Contract {i} → Contract {↑ i}
  Let : {i : Size} → ValueId → Value → Contract {i} → Contract {↑ i}
  Assert : {i : Size} → Observation → Contract {i} → Contract {↑ i}


getAction : Case → Action
getAction (mkCase action _) = action

maxTimeout : {i : Size} → Contract {i}  → ℕ
maxTimeout Close = 0
maxTimeout (Pay _ _ _ _ c) = maxTimeout c
maxTimeout (If _ c₁ c₂) = maxTimeout c₁ ⊔ maxTimeout c₂
maxTimeout (When [] (mkTimeout (mkPosixTime t)) c) = t ⊔ maxTimeout c
maxTimeout (When ((mkCase _ x) ∷ xs) t c) = maxTimeout x ⊔ maxTimeout (When xs t c)
maxTimeout (Let x x₁ c) = maxTimeout c
maxTimeout (Assert x c) = maxTimeout c
