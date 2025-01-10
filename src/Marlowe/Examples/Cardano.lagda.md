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
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Class.DecEq
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

open import Marlowe.Language impl public
open import Marlowe.Semantics.Evaluate impl public
open import Marlowe.Semantics.Reduce impl public
open import Marlowe.Semantics.Operate impl public
```

## Evaluation

```agda
evalValue : Environment → State → Value → ℤ
evalObservation : Environment → State → Observation → Bool

evalValue e s v = ℰ⟦ v ⟧ e s
evalObservation e s o = 𝒪⟦ o ⟧ e s
```
