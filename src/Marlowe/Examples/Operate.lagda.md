---
title: Marlowe.Examples.Operate
layout: page
---

```
module Marlowe.Examples.Operate where
```

## Imports

```
open import Data.Integer as ℤ using (+_)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.String using (String; _≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Decidable; DecidableEquality)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Marlowe.Language.Contract as Contract
open import Marlowe.Language.Input as Input
open import Marlowe.Language.State as State
open import Marlowe.Language.Transaction as Transaction
```

### Token and Party

`Token` and `Party` here are simply strings.

```
open Contract.Parameterized {String} {String}
open Input.Parameterized {String} {String}
open State.Parameterized {String} {String}
open Transaction.Parameterized {String} {String}

open import Marlowe.Semantics.Reduce _≟_ _≟_
open import Marlowe.Semantics.Operate _≟_ _≟_
```

### Example

```
tₒ : PosixTime
tₒ = mkPosixTime 100

p₁ : String
p₁ = "party₁"

p₂ : String
p₂ = "party₂"

a₁ : AccountId
a₁ = mkAccountId p₁

a₂ : AccountId
a₂ = mkAccountId p₂

t : String
t = "token"

v : Value
v = Constant (+ 1)

d : Contract
d = When ([ mkCase (Deposit a₁ p₂ t v) Close ]) (mkTimeout tₒ) Close

c : Contract
c = Assert FalseObs d

s : State
s = emptyState (mkPosixTime 0)

i : TransactionInput
i = mkTransactionInput (mkInterval (mkPosixTime 0) 10) [ NormalInput (IDeposit a₁ p₂ t 1) ]

e : Environment
e = mkEnvironment (mkInterval (mkPosixTime 0) 2)

reduction-steps :
  (c , s)
  ⇓ ⟦ [ TransactionAssertionFailed ]
    , [ a₁ [ t , 1 ]↦ mkParty p₁ ]
    , s
    ⟧
reduction-steps =
  reduce-until-quiescent refl refl
    (⟪ c , s , e , [] , [] ⟫ ⇀⟨ AssertFalse refl ⟩ (⟪ d , s , e , [ ReduceAssertionFailed ] , [] ⟫ ∎))
    (waiting (s≤s (s≤s (s≤s z≤n))))
    (apply-input {i = NormalInput (IDeposit a₁ p₂ t 1)} (s≤s (s≤s (s≤s z≤n))) (trim-interval z≤n)
      (Deposit (here refl) refl (s≤s (s≤s (s≤s z≤n))) close
        (⟪ Close , ⟨ [((a₁ , t) , 1)] , [] , [] , mkPosixTime 0 ⟩ , e , []  , [] ⟫
               ⇀⟨ CloseRefund ⟩ (⟪ Close , ⟨ [] , [] , [] , mkPosixTime 0 ⟩ , e , [] , [ a₁ [ t , 1 ]↦ mkParty p₁ ] ⟫) ∎))
      (done refl))

_ = ⇓-eval c s (i ∷ []) ≡
     inj₁ (
       ⟦ [ TransactionAssertionFailed ]
       , [ a₁ [ t , 1 ]↦ mkParty p₁ ]
       , s
       ⟧ , reduction-steps)
```
