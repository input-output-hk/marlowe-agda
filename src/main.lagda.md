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
open import Data.Unit
open import Data.Product
open import Data.String
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (case_of_)

open import Marlowe.Examples.Escrow
open import Marlowe.Language
open PartyParam Party
open TokenParam Token
open import Marlowe.Semantics.Operate _≟-Party_ _≟-Token_
```

### Haskell reference implemenation

The reference implementation in Haskell is used for serialization 

```
{-# FOREIGN GHC import Marlowe.Core.Contract #-}

postulate
  printContract : Contract → String
{-# COMPILE GHC printContract = printContract #-}
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
      λ { (inj₁ (⟦ ws , ps , s ⟧ , steps)) → putStrLn (printContract contract)
        ; (inj₂ e) → putStrLn "error"
        }
    )
```


