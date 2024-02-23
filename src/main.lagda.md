---
title: main
layout: page
---

```
{-# OPTIONS --guardedness #-}

module main where
```


## Imports

```
open import IO
open List using (forM′)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (case_of_; _∘_)

open import Marlowe.Examples.Escrow
open import Marlowe.Language
open PartyParam Party
open TokenParam Token
open import Marlowe.Semantics.Operate _≟-Party_ _≟-Token_
```

### Haskell reference implementation

The reference implementation in Haskell is used for serialization 

```
{-# FOREIGN GHC import Marlowe.Core.Contract #-}

postulate
  showContract : Contract → String
  showPayment : Payment → String
{-# COMPILE GHC showContract = showContract #-}
{-# COMPILE GHC showPayment = showPayment #-}
```

## Main

```
main : Main
main =
  let
    (minTime , contract , inputs) = escrowExample
    r = ⇓-eval contract (emptyState minTime) inputs
  in run (
    case r of
      λ { (inj₁ (⟦ ws , ps , s ⟧ , steps)) →
             putStrLn (showContract contract)
          >> forM′ ps (putStrLn ∘ showPayment)
        ; (inj₂ e) → putStrLn "error"
        }
    )
```

