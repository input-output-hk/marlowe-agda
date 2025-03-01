module Marlowe.Abstract where

open import Class.DecEq

record MarloweAbstract : Set₁ where
  field Token : Set
        ⦃ DecEq-Token ⦄ : DecEq Token
        
        Party : Set
        ⦃ DecEq-Party ⦄ : DecEq Party
