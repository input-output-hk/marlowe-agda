---
title: Marlowe.Examples.Escrow
layout: page
---

```
module Marlowe.Examples.Escrow where
```

## Imports

```
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)
open import Data.Integer using (0ℤ; 1ℤ; +_)
open import Data.Nat as ℕ
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.String as String
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Marlowe.Language.Contract as C
open import Marlowe.Language.Input as I
open import Marlowe.Language.State as S
open import Marlowe.Language.Transaction as T
```

```
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
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
Address b₁ ≟-Party Address b₂ with b₁ String.≟ b₂
... | yes p = yes (cong Address p)
... | no ¬p = no λ x → let y = cong unParty x in ¬p y
Role b₁ ≟-Party Role b₂ with b₁ String.≟ b₂
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
mkToken c₁ n₁ ≟-Token mkToken c₂ n₂ with c₁ String.≟ c₂ | n₁ String.≟ n₂
... | yes p | yes q = yes (cong₂ mkToken p q)
... | _ | no ¬q = no λ x → ¬q (cong getTokenName x)
... | no ¬p | _ = no λ x → ¬p (cong getCurrencySymbol x)
```

```
open C.Domain _≟-Party_ _≟-Token_
open S.Domain _≟-Party_ _≟-Token_
open T.Domain _≟-Party_ _≟-Token_
open I.Domain _≟-Party_ _≟-Token_
```

## Escrow

```
escrow : Party → Party → Party → Token → ℕ → Timeout → Timeout → Timeout → Timeout → Contract
escrow seller buyer mediator token price paymentDeadline complaintDeadline responseDeadline mediationDeadline =
  When
    [
      mkCase (Deposit (mkAccountId seller) buyer token price')
        (
          When
            [
              mkCase (makeChoice "Everything is alright" buyer 0ℤ)
                Close
            , mkCase (makeChoice "Report problem" buyer 1ℤ)
                (
                  Pay (mkAccountId seller) (mkAccount (mkAccountId buyer)) token price'
                    (
                      When
                        [
                          mkCase (makeChoice "Confirm problem" seller 1ℤ)
                            Close
                        , mkCase (makeChoice "Dispute problem" seller 0ℤ)
                            (
                              When
                                [
                                  mkCase (makeChoice "Dismiss claim" mediator 0ℤ)
                                    (
                                      Pay (mkAccountId buyer) (mkAccount (mkAccountId seller)) token price'
                                        Close
                                    )
                                , mkCase (makeChoice "Confirm claim" mediator 1ℤ)
                                    Close
                                ]
                                mediationDeadline
                                Close
                            )
                        ]
                        responseDeadline
                        Close
                    )
                )
            ]
            complaintDeadline
            Close
        )
    ]
    paymentDeadline
    Close
  where
    price' : Value
    price' = Constant (+ price)
    makeChoice : String → Party → Int → Action
    makeChoice name party value = Choice (mkChoiceId (mkChoiceName name) party) [(mkBound value value)]
```

```
escrowExample : PosixTime × Contract × (List TransactionInput)
escrowExample =
  let
    seller = Role "Seller"
    buyer = Role "Buyer"
    mediator = Role "Mediator"
    token = mkToken "" ""
    price = 1000
    interval = mkInterval (mkPosixTime 0) 5
  in
    ⟨ (mkPosixTime 0)
    , ⟨ escrow seller buyer mediator token price
          (mkTimeout (mkPosixTime 10))
          (mkTimeout (mkPosixTime 20))
          (mkTimeout (mkPosixTime 30))
          (mkTimeout (mkPosixTime 40))
      , [
        mkTransactionInput interval [(NormalInput (IDeposit (mkAccountId seller) buyer token price))]
      , mkTransactionInput interval [(NormalInput (IChoice (mkChoiceId (mkChoiceName "Everything is alright") buyer) (mkChosenNum 0ℤ)))]
      ]
    ⟩ ⟩
```
