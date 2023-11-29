module Marlowe.Semantics.Operate.Properties where

open import Data.List using ([])
open import Data.List.Properties using (++-identityˡ-unique)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

open import Marlowe.Language.Contract
open import Marlowe.Semantics.Reduce
open import Marlowe.Semantics.Reduce.Properties
open import Marlowe.Semantics.Operate

-- A transaction on a closed contract does not produce any warning
⇓Close-is-safe :
  ∀ {e} {i} {s} {ws} {ps}
  → e ⊢ ( Close , i , s ) ⇓ ⟦ ws , ps , s ⟧
  → ws ≡ []
⇓Close-is-safe (⇓-Reduce-until-quiescent {ws₂ = ws₂} (reduce-until-quiescent x _) y) rewrite ⇀⋆Close-is-terminal x rewrite ⇓Close-is-safe y =
  cong convertReduceWarnings (++-identityˡ-unique ws₂ (⇀⋆Close-is-safe x))
⇓Close-is-safe (⇓-Close _ _) = refl
