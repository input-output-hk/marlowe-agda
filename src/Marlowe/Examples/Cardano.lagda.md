```agda
module Marlowe.Examples.Cardano where
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
open import Marlowe.Semantics.Evaluate impl
open import Marlowe.Semantics.Reduce impl
open import Marlowe.Semantics.Operate impl
```

## Evaluation

```agda
evalValue : Environment → State → Value → ℤ
evalObservation : Environment → State → Observation → Bool

evalValue e s v = ℰ⟦ v ⟧ e s
evalObservation e s o = 𝒪⟦ o ⟧ e s
```
<!--
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

  HSTy-Observation : HasHsType Observation
  HSTy-Value : HasHsType Value

  HSTy-Observation = autoHsType Observation
  HSTy-Value = autoHsType Value

  {-# TERMINATING #-}
  Conv-Observation : let type = HasHsType.HsType HSTy-Observation in Convertible Observation type

  {-# TERMINATING #-}
  Conv-Value : let type = HasHsType.HsType HSTy-Value in Convertible Value type

  Conv-Observation = autoConvert Observation
  Conv-Value = autoConvert Value

  HSTy-Bound = autoHsType Bound
  Conv-Bound = autoConvert Bound

  HSTy-Action = autoHsType Action
  Conv-Action = autoConvert Action

  HSTy-Case : HasHsType Case
  HSTy-Contract : HasHsType Contract

  HSTy-Case = autoHsType Case
  HSTy-Contract = autoHsType Contract

  {-# TERMINATING #-}
  Conv-Case : let type = HasHsType.HsType HSTy-Case in Convertible Case type

  {-# TERMINATING #-}
  Conv-Contract : let type = HasHsType.HsType HSTy-Contract in Convertible Contract type

  Conv-Case = autoConvert Case
  Conv-Contract = autoConvert Contract

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
eval-value : HsType (Environment → State → Value → ℤ)
eval-value = to evalValue
{-# COMPILE GHC eval-value as evalValue #-}

eval-observation : HsType (Environment → State → Observation → Bool)
eval-observation = to evalObservation
{-# COMPILE GHC eval-observation as evalObservation #-}

open import Data.Maybe
open import Data.Sum
open import Data.Product

evalBs : Contract → State → List TransactionInput → Maybe Result
evalBs c s is
  with ⇓-eval c s is
... | inj₁ (i , _) = just i
... | inj₂ _ = nothing

instance
  HSTy-Result = autoHsType Result ⊣ withConstructor "MkResult"
  Conv-Result = autoConvert Result

eval-bs : HsType (Contract → State → List TransactionInput → Maybe Result)
eval-bs = to evalBs
{-# COMPILE GHC eval-bs as evalBs #-}
```
-->
