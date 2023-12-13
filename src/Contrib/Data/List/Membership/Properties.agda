module Contrib.Data.List.Membership.Properties where

open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)

∈-∷ :
  ∀ {A : Set} {x : A} {a : A} {as : List A}
  → x ∈ as
  --------------
  → x ∈ (a ∷ as)
∈-∷ (here refl) = there (here refl)
∈-∷ (there x) = there (∈-∷ x)
