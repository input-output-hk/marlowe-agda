```agda
module Marlowe.Examples.Cardano where

{-# FOREIGN GHC
  {-# LANGUAGE DuplicateRecordFields #-}
#-}

```

<!--
## Imports

```agda
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.List using (List)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Class.DecEq

open import Function.Base using (id)

open import Tactic.Derive.Convertible
open import Tactic.Derive.HsType

open import Class.Convertible
open import Class.HasHsType
open import Prelude.AssocList
```
-->

## Party

```agda
data Party : Set where
  Address : String → Party
  Role : String → Party

unParty : Party → String
unParty (Address x) = x
unParty (Role x) = x

instance
  DecEq-Party : DecEq Party
  DecEq-Party = record { _≟_ = _≟-Party_ }
    where
      _≟-Party_ : DecidableEquality Party
      Address b₁ ≟-Party Address b₂ with b₁ ≟ b₂
      ... | yes p = yes (cong Address p)
      ... | no ¬p = no λ x → let y = cong unParty x in ¬p y
      Role b₁ ≟-Party Role b₂ with b₁ ≟ b₂
      ... | yes p = yes (cong Role p)
      ... | no ¬p = no λ x → let y = cong unParty x in ¬p y
      Role _ ≟-Party Address _ = no λ ()
      Address _ ≟-Party Role _ = no λ ()
```

## Token

```agda
data Token : Set where
  mkToken : String → String → Token

getCurrencySymbol : Token → String
getCurrencySymbol (mkToken c _) = c

getTokenName : Token → String
getTokenName (mkToken _ n) = n

instance
  DecEq-Token : DecEq Token
  DecEq-Token = record { _≟_ = _≟-Token_ }
    where
      _≟-Token_ : DecidableEquality Token
      mkToken c₁ n₁ ≟-Token mkToken c₂ n₂ with c₁ ≟ c₂ | n₁ ≟ n₂
      ... | yes p | yes q = yes (cong₂ mkToken p q)
      ... | _ | no ¬q = no λ x → ¬q (cong getTokenName x)
      ... | no ¬p | _ = no λ x → ¬p (cong getCurrencySymbol x)
```

```agda
open import Marlowe.Abstract

impl : MarloweAbstract
impl =
  record
    { Token = Token
    ; Party = Party
    }

open import Marlowe.Language impl
  renaming (Value to ValueAgda; Observation to ObservationAgda;
    Contract to ContractAgda; Case to CaseAgda) public
open import Marlowe.Semantics.Evaluate impl public
open import Marlowe.Semantics.Reduce impl public
open import Marlowe.Semantics.Operate impl public
```

## Evaluation

```agda
evalValue : Environment → State → ValueAgda → ℤ
evalObservation : Environment → State → ObservationAgda → Bool

evalValue e s v = ℰ⟦ v ⟧ e s
evalObservation e s o = 𝒪⟦ o ⟧ e s
```
## Export to Haskell

```agda
instance
  HsTy-ℤ = MkHsType ℤ ℤ

  Conv-ℤ : Convertible ℤ ℤ
  Conv-ℤ =
    let open Convertible in λ where
      .to   → id
      .from → id

  Convertible-String : Convertible String String
  Convertible-String =
    let open Convertible in λ where
      .to   → id
      .from → id

  Convertible-Bool : Convertible Bool Bool
  Convertible-Bool =
    let open Convertible in λ where
      .to   → id
      .from → id

  HSTy-PosixTime = autoHsType PosixTime
  Conv-PosixTime = autoConvert PosixTime

  HSTy-Timeout = autoHsType Timeout
  Conv-timeout = autoConvert Timeout

  HSTy-Party = autoHsType Party
  Conv-Party = autoConvert Party

  HSTy-Token = autoHsType Token
  Conv-Token = autoConvert Token

  HSTy-AccountId = autoHsType AccountId
  Conv-AccountId = autoConvert AccountId

  HSTy-ChoiceName = autoHsType ChoiceName
  Conv-ChoiceName = autoConvert ChoiceName

  HSTy-ChoiceId = autoHsType ChoiceId
  Conv-ChoiceId = autoConvert ChoiceId

  HSTy-ValueId = autoHsType ValueId
  Conv-ValueId = autoConvert ValueId

  HSTy-Payee = autoHsType Payee
  Conv-Payee = autoConvert Payee

  -- Mutually recursive type see:
  -- https://github.com/agda/agda-stdlib-meta/issues/19

  HSTy-Observation : HasHsType ObservationAgda
  HSTy-Value : HasHsType ValueAgda

{-# FOREIGN GHC
data Observation =
    AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseSomething ChoiceId
  | ValueGE Value Value
  | ValueGT Value Value
  | ValueLT Value Value
  | ValueLE Value Value
  | ValueEQ Value Value
  | TrueObs
  | FalseObs
  deriving (Show, Eq, Generic)
data Value =
    AvailableMoney AccountId Token
  | Constant Integer
  | NegValue Value
  | AddValue Value Value
  | SubValue Value Value
  | MulValue Value Value
  | DivValue Value Value
  | ChoiceValue ChoiceId
  | TimeIntervalStart
  | TimeIntervalEnd
  | UseValue ValueId
  | Cond Observation Value Value
  deriving (Show, Eq, Generic)
#-}

data Value : Set
data Observation : Set

data Value where
  AvailableMoney : HasHsType.HsType HSTy-AccountId → HasHsType.HsType HSTy-Token → Value
  Constant : ℤ → Value
  NegValue : Value → Value
  AddValue : Value → Value → Value
  SubValue : Value → Value → Value
  MulValue : Value → Value → Value
  DivValue : Value → Value → Value
  ChoiceValue : HasHsType.HsType HSTy-ChoiceId → Value
  TimeIntervalStart : Value
  TimeIntervalEnd : Value
  UseValue : HasHsType.HsType HSTy-ValueId → Value
  Cond : Observation → Value → Value → Value
  
data Observation where
  AndObs : Observation → Observation → Observation
  OrObs : Observation → Observation → Observation
  NotObs : Observation → Observation
  ChoseSomething : HasHsType.HsType HSTy-ChoiceId → Observation
  ValueGE : Value → Value → Observation
  ValueGT : Value → Value → Observation
  ValueLT : Value → Value → Observation
  ValueLE : Value → Value → Observation
  ValueEQ : Value → Value → Observation
  TrueObs : Observation
  FalseObs : Observation

{-# COMPILE GHC Value = data Value (AvailableMoney | Constant | NegValue | AddValue | SubValue | MulValue | DivValue | ChoiceValue | TimeIntervalStart | TimeIntervalEnd | UseValue | Cond) #-}
{-# COMPILE GHC Observation = data Observation (AndObs | OrObs | NotObs | ChoseSomething | ValueGE | ValueGT | ValueLT | ValueLE | ValueEQ | TrueObs | FalseObs) #-}

instance
  HSTy-Observation = MkHsType ObservationAgda Observation
  HSTy-Value = MkHsType ValueAgda Value

  Conv-Observation : Convertible ObservationAgda Observation
  {-# TERMINATING #-}
  Conv-Value : Convertible ValueAgda Value

  Conv-Observation = autoConvert ObservationAgda
  Conv-Value = autoConvert ValueAgda

  HSTy-Bound = autoHsType Bound
  Conv-Bound = autoConvert Bound

  HSTy-Action = autoHsType Action
  Conv-Action = autoConvert Action

{-# FOREIGN GHC

data Case = MkCase Action Contract
  deriving (Show, Eq, Generic)
data Contract = 
    Close  
  | Pay AccountId Payee Token Value Contract
  | If Observation Contract Contract
  | When [Case] Timeout Contract
  | Let ValueId Value Contract
  | Assert Observation Contract
  deriving (Show, Eq, Generic)
#-}

data Case : Set
data Contract : Set

data Case where
  MkCase : HasHsType.HsType HSTy-Action → Contract → Case

data Contract where
  Close : Contract
  Pay : HasHsType.HsType HSTy-AccountId → HasHsType.HsType HSTy-Payee → HasHsType.HsType HSTy-Token → Value → Contract → Contract
  If : Observation → Contract → Contract → Contract
  When : List Case → HasHsType.HsType HSTy-Timeout → Contract → Contract
  Let : HasHsType.HsType HSTy-ValueId → Value → Contract → Contract
  Assert : Observation → Contract → Contract

{-# COMPILE GHC Case = data Case (MkCase) #-}
{-# COMPILE GHC Contract = data Contract (Close | Pay | If | When | Let | Assert) #-}

instance
  HSTy-Case : HasHsType CaseAgda
  HSTy-Contract : HasHsType ContractAgda

  HSTy-Case = MkHsType CaseAgda Case
  HSTy-Contract = MkHsType ContractAgda Contract

  Conv-Case : Convertible CaseAgda Case
  {-# TERMINATING #-}
  Conv-Contract : Convertible ContractAgda Contract

  Conv-Case = autoConvert CaseAgda
  Conv-Contract = autoConvert ContractAgda

  HSTy-TimeInterval = autoHsType TimeInterval
  Conv-TimeInterval = autoConvert TimeInterval

  HSTy-Environment = autoHsType Environment
  Conv-Environment = autoConvert Environment

  HSTy-State = autoHsType State ⊣ withConstructor "MkState"
  Conv-State = autoConvert State

  HSTy-Payment = autoHsType Payment ⊣ withConstructor "MkPayment"
  Conv-Payment = autoConvert Payment

  HSTy-ChosenNum = autoHsType ChosenNum
  Conv-ChosenNum = autoConvert ChosenNum

  HSTy-Input = autoHsType Input
  Conv-Input = autoConvert Input

  HSTy-TransactionWarning = autoHsType TransactionWarning
  Conv-TransactionWarning = autoConvert TransactionWarning

  HSTy-IntervalError = autoHsType IntervalError
  Conv-IntervalError = autoConvert IntervalError

  HSTy-TransactionError = autoHsType TransactionError
  Conv-TransactionError = autoConvert TransactionError

  HSTy-TransactionOutput = autoHsType TransactionOutput
  Conv-TransactionOutput = autoConvert TransactionOutput

  HSTy-TransactionInput = autoHsType TransactionInput
  Conv-TransactionInput = autoConvert TransactionInput
```
```agda
eval-value : HsType (Environment → State → ValueAgda → ℤ)
eval-value = to evalValue
{-# COMPILE GHC eval-value as evalValue #-}

eval-observation : HsType (Environment → State → ObservationAgda → Bool)
eval-observation = to evalObservation
{-# COMPILE GHC eval-observation as evalObservation #-}

open import Data.Maybe
open import Data.Sum
open import Data.Product

evalBs : ContractAgda → State → List TransactionInput → Maybe Result
evalBs c s is
  with ⇓-eval c s is
... | inj₁ (i , _) = just i
... | inj₂ _ = nothing

instance
  HSTy-Result = autoHsType Result ⊣ withConstructor "MkResult"
  Conv-Result = autoConvert Result

eval-bs : HsType (ContractAgda → State → List TransactionInput → Maybe Result)
eval-bs = to evalBs
{-# COMPILE GHC eval-bs as evalBs #-}
```
