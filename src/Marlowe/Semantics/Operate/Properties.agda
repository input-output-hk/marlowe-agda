module Marlowe.Semantics.Operate.Properties where

open import Data.List using ([]; _∷_)
open import Data.List.Properties using (++-identityˡ-unique)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
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
  ∀ {c : Contract} {e} {i : TransactionInput} {s : State} {D D′ : Result}
  → e ⊢ (c , i , s) ⇓ D
  → e ⊢ (c , i , s) ⇓ D′
  → D ≡ D′
⇓-deterministic (⇓-Deposit (here refl) n₁ t₁ x) (⇓-Deposit (here refl) n₂ t₂ y) = ⇓-deterministic x y
⇓-deterministic (⇓-Deposit {cont = cont} (there c₁) n₁ t₁ x) (⇓-Deposit {cont = cont} (there c₂) n₂ t₂ y) = ⇓-deterministic (⇓-Deposit {cont = cont} c₁ n₁ t₁ x) (⇓-Deposit c₂ n₂ t₂ y)
⇓-deterministic (⇓-Choice _ _ _ x) (⇓-Choice _ _ _ y) = {!!}
⇓-deterministic (⇓-Notify _ _ _ x) (⇓-Notify _ _ _ y) = {!!}
⇓-deterministic (⇓-Reduce-until-quiescent _ x) (⇓-Reduce-until-quiescent _ y) = {!!}
⇓-deterministic (⇓-Close _ _) (⇓-Close _ _) = refl
⇓-deterministic _ _ = {!!}
-}

-- A transaction on a closed contract does not produce any warning
⇓-Close-is-safe :
  ∀ {e} {i} {s₀ s₁} {ws} {ps}
  → e ⊢ ( Close , i , s₀ ) ⇓ ⟦ ws , ps , s₁ ⟧
  → ws ≡ []
⇓-Close-is-safe (⇓-Reduce-until-quiescent {ws₂ = ws₂} (reduce-until-quiescent x _) y) rewrite ⇀⋆Close-is-terminal x rewrite ⇓-Close-is-safe y =
  cong convertReduceWarnings (++-identityˡ-unique ws₂ (⇀⋆Close-is-safe x))
⇓-Close-is-safe (⇓-Close _ _) = refl
