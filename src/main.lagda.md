---
title: main
layout: page
---

```agda
{-# OPTIONS --guardedness #-}

module main where
```


## Imports

```agda
open import IO
open List using (forM′)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (case_of_; _∘_)

open import Marlowe.Language
open import Marlowe.Examples.Cardano
open import Marlowe.Examples.Escrow

open Entities-Parameterized-by-Party {Party}
open Entities-Parameterized-by-Token {Token}
open import Marlowe.Semantics.Operate _≟-Party_ _≟-Token_
```

### Haskell reference implementation

The reference implementation in Haskell is used for serialization 

```agda
{-# FOREIGN GHC import Marlowe.Core.Contract #-}

postulate
  showContract : Contract → String
  showPayment : Payment → String
  contractJSON : Contract → String
{-# COMPILE GHC showContract = showContract #-}
{-# COMPILE GHC showPayment = showPayment #-}
{-# COMPILE GHC contractJSON = contractJSON #-}
```

## Main

```agda
main : Main
main =
  let
    (minTime , contract , inputs) = escrowExample
    r = ⇓-eval contract (emptyState minTime) inputs
  in run (
    case r of
      λ { (inj₁ (⟦ ws , ps , s ⟧ , steps)) →
            putStrLn (contractJSON contract)
          >> forM′ ps (putStrLn ∘ showPayment)
        ; (inj₂ e) → putStrLn "error"
        }
    )
```


