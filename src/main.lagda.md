---
title: main
layout: page
---

```
module main where
```

## Imports

```
open import Data.Product
open import Data.String
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (case_of_)

open import Marlowe.Examples.Escrow
open import Marlowe.Language
open PartyParam Party
open TokenParam Token
open import Marlowe.Semantics.Operate _≟-Party_ _≟-Token_

{-# FOREIGN GHC import qualified System.IO #-}

postulate FileHandle : Set
{-# COMPILE GHC FileHandle = type System.IO.Handle #-}

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

{-# FOREIGN GHC
  import qualified Data.Text.IO as Text
  import qualified System.IO as IO
#-}

postulate
  stdout    : FileHandle
  hPutStrLn : FileHandle → String → IO ⊤
{-# COMPILE GHC stdout    = IO.stdout #-}
{-# COMPILE GHC hPutStrLn = Text.hPutStrLn #-}

{-# FOREIGN GHC import Marlowe.Core.Contract #-}

postulate
  printContract : Contract → String
{-# COMPILE GHC printContract = printContract #-}

main : IO ⊤
main =
  let
    (minTime , contract , inputs) = escrowExample
    r = ⇓-eval contract (emptyState minTime) inputs
  in
    case r of
      λ { (inj₁ (⟦ ws , ps , s ⟧ , steps)) → hPutStrLn stdout (printContract contract)
        ; (inj₂ e) → hPutStrLn stdout "error"
        }
```


