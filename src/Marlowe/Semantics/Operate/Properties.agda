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

open Configuration
open TransactionInput

⇒-Quiescent : ∀ {C D i}
  → (C , i) ⇒ D
  → Quiescent D
⇒-Quiescent (Deposit _ _ _ x) = ⇒-Quiescent x
⇒-Quiescent (Choice _ _ _ x) = ⇒-Quiescent x
⇒-Quiescent (Notify _ _ _ x) = ⇒-Quiescent x
⇒-Quiescent (Reduce-until-quiescent _ q) = q

-- A transaction on a closed contract does not produce any warning
⇒-Close-is-safe :
  ∀ {C D i}
  → (C , i) ⇒ D
  → contract C ≡ Close
  → warnings C ≡ warnings D
⇒-Close-is-safe (Reduce-until-quiescent C⇀⋆D _) refl = ⇀⋆Close-is-safe C⇀⋆D

⇒-Close-is-terminal :
  ∀ {C D i}
  → (C , i) ⇒ D
  → contract C ≡ Close
  → contract D ≡ Close
⇒-Close-is-terminal (Reduce-until-quiescent C⇀⋆D _) refl = ⇀⋆Close-is-terminal C⇀⋆D

{-
⇓-Close-is-safe :
  ∀ {e s r}
  → e ⊢ (Close , s) ⇓ r
  → (Result.warnings r) ≡ []
⇓-Close-is-safe (done _) = refl
⇓-Close-is-safe (apply-input {i} {C} {D} {ws} {ps} {s} x y) rewrite ⇒-Close-is-terminal x refl =
  let yy = ⇓-Close-is-safe y
      xx = ⇒-Close-is-safe x refl
  in {!!}
-}
