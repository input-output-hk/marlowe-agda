---
title: Marlowe.Examples.Escrow
layout: page
---

```agda
module Marlowe.Examples.Escrow where
```

<!--
## Imports

```agda
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)
open import Data.Integer using (0ℤ; 1ℤ; +_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )

open import Marlowe.Examples.Cardano
```
-->

```agda
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
```

```agda
open import Marlowe.Language
open Entities-Parameterized-by-Party {Party}
open Entities-Parameterized-by-Token {Token}
```

## Escrow

```agda
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

```agda
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
