module Contrib.DecEq where

open import Level
open import Data.Bool using (Bool; not)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (⌊_⌋)

variable
  ℓ : Level

record DecEq (A : Set ℓ) : Set ℓ where
  field _≟_ : DecidableEquality A

  _==_ _≡ᵇ_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋
  _≡ᵇ_ = _==_

  _≠_ : A → A → Bool
  x ≠ y = not (x == y)

  infix 4 _≟_ _≡ᵇ_ _==_ _≠_
open DecEq ⦃...⦄ public

open import Data.String

instance
  DecEq-String : DecEq String
  DecEq-String = record { _≟_ = Data.String._≟_ }
