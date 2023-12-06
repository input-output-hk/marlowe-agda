module Marlowe.Semantics.Operate.Properties where

open import Data.List using ([]; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
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
⇒-Quiescent (Deposit _ _ _ (Reduce-until-quiescent C⇀⋆D q)) = q
⇒-Quiescent (Choice _ _ _ (Reduce-until-quiescent C⇀⋆D q)) = q
⇒-Quiescent (Notify _ _ _ (Reduce-until-quiescent C⇀⋆D q)) = q

⇓-Close-is-safe :
  ∀ {s r}
  → (Close , s) ⇓ r
  → (Result.warnings r) ≡ []
⇓-Close-is-safe (done _) = refl
⇓-Close-is-safe (reduce-until-quiescent refl refl x y)
  rewrite ↠-Close-is-terminal x refl rewrite ⇓-Close-is-safe y =
    trans (cong (convertReduceWarnings) (sym (↠-Close-is-safe x refl))) refl
