---
title: Marlowe.Examples.Cardano
layout: page
---

```
module Marlowe.Examples.Cardano where
```

## Imports

```
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.String using (_≟_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Relation.Nullary using (yes; no)
```

## Party

```
data Party : Set where
  Address : String → Party
  Role : String → Party

unParty : Party → String
unParty (Address x) = x
unParty (Role x) = x

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

```
data Token : Set where
  mkToken : String → String → Token

getCurrencySymbol : Token → String
getCurrencySymbol (mkToken c _) = c

getTokenName : Token → String
getTokenName (mkToken _ n) = n

_≟-Token_ : DecidableEquality Token
mkToken c₁ n₁ ≟-Token mkToken c₂ n₂ with c₁ ≟ c₂ | n₁ ≟ n₂
... | yes p | yes q = yes (cong₂ mkToken p q)
... | _ | no ¬q = no λ x → ¬q (cong getTokenName x)
... | no ¬p | _ = no λ x → ¬p (cong getCurrencySymbol x)
```

```
open import Marlowe.Language
open Entities-Parameterized-by-Party {Party}
open Entities-Parameterized-by-Token {Token}

open import Marlowe.Semantics.Evaluate _≟-Party_ _≟-Token_
```

```
{-# FOREIGN GHC import Marlowe.Core.Contract #-}
{-# COMPILE GHC Party = data Party (Address | Role) #-}
{-# COMPILE GHC Token = data Token (Token) #-}
```

## Evaluation

```

evalValue : Value → Environment → State → ℤ
evalObservation : Observation → Environment → State → Bool

evalValue v e s = ℰ⟦ v ⟧ e s
evalObservation o e s = 𝒪⟦ o ⟧ e s

-- TODO: functions to be used in test-spec
-- {-# COMPILE GHC evalValue as evalValue #-}
-- {-# COMPILE GHC evalObservation as evalObservation #-}
