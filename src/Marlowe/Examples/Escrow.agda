

module Marlowe.Examples.Escrow where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)
open import Data.Integer using (0ℤ; 1ℤ; +_)
open import Data.List using (List; []; _∷_)
open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.Transaction
open import Primitives


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []


escrow : Party → Party → Party → Token → Int → Timeout → Timeout → Timeout → Timeout → Contract
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
    price' = Constant price
    makeChoice : String → Party → Int → Action
    makeChoice name party value = Choice (mkChoiceId (mkChoiceName (mkByteString name)) party) [(mkBound value value)]


escrowExample : Triple PosixTime Contract (List TransactionInput)
escrowExample =
  let
    seller = Role (mkByteString "Seller")
    buyer = Role (mkByteString "Buyer")
    mediator = Role (mkByteString "Mediator")
    token = mkToken (mkByteString "") (mkByteString"")
    price = + 1000
    interval = pair (mkPosixTime (+ 0)) (mkPosixTime (+ 5))
  in
    triple
      (mkPosixTime 0ℤ)
      (
        escrow seller buyer mediator token price
          (mkTimeout (mkPosixTime (+ 10)))
          (mkTimeout (mkPosixTime (+ 20)))
          (mkTimeout (mkPosixTime (+ 30)))
          (mkTimeout (mkPosixTime (+ 40)))
      )
      [
        mkTransactionInput interval [(NormalInput (IDeposit (mkAccountId seller) buyer token price))]
      , mkTransactionInput interval [(NormalInput (IChoice (mkChoiceId (mkChoiceName (mkByteString "Everything is alright")) buyer) (mkChosenNum 0ℤ)))]
      ]
