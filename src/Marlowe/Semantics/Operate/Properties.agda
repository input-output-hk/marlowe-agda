module Marlowe.Semantics.Operate.Properties where

open import Data.List using ([]; _∷_)
open import Data.List.Properties using (++-identityʳ; ++-identityˡ-unique)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Marlowe.Language.Contract
open import Marlowe.Language.State
open import Marlowe.Language.Transaction

open import Marlowe.Semantics.Reduce
open import Marlowe.Semantics.Reduce.Properties
open import Marlowe.Semantics.Operate

open TransactionInput

{-
⇓-deterministic :
  ∀ {c : Contract} {e} {i : TransactionInput} {s : State} {r r′}
  → e ⊢ (c , i , s) ⇓ r
  → e ⊢ (c , i , s) ⇓ r′
  → r ≡ r′
-}

-- A transaction on a closed contract does not produce any warning
⇓-Close-is-safe :
  ∀ {e} {i} {s} {ws ps c x}
  → e ⊢ ( Close , i , s ) ⇓ ( c , ⟦ ws , ps , x ⟧ )
  → ws ≡ []
⇓-Close-is-safe (⇓-Reduce-until-quiescent {ws = ws} C⇀⋆D _ refl refl)
   = cong convertReduceWarnings (++-identityˡ-unique ws (⇀⋆Close-is-safe C⇀⋆D))
