

module Marlowe.Language.Input where


open import Agda.Builtin.Int using (Int)
open import Marlowe.Language.Contract using (AccountId; ChoiceId; Party; Token)


data ChosenNum : Set where
  mkChosenNum : Int → ChosenNum


data InputContent : Set where
  IDeposit : AccountId → Party → Token → Int → InputContent
  IChoice : ChoiceId → ChosenNum → InputContent
  INotify : InputContent


data Input : Set where
  NormalInput : InputContent → Input
