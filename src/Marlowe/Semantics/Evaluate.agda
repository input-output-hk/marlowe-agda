module Marlowe.Semantics.Evaluate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int)
open import Data.Bool using (_∧_; _∨_; if_then_else_; not)
open import Data.Integer using (-_; _+_; _-_; _*_; _≟_; _<?_; _≤?_; ∣_∣; 0ℤ; NonZero)
open import Data.Integer.DivMod using (_div_)
open import Data.Maybe using (fromMaybe)
open import Data.Nat as ℕ using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Integer using (0ℤ; 1ℤ; +_)
open import Relation.Nullary using (_because_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Marlowe.Language.Contract
open import Marlowe.Language.State

open Environment using (timeInterval)
open TimeInterval using (startTime; offset)
open State using (accounts; boundValues; choices)

open import Primitives
open Decidable _≟-AccountId×Token_  renaming (_‼_default_ to _‼ᵃ_default_) hiding (_∈?_)
open Decidable _≟-ChoiceId_ renaming (_‼_default_ to _‼ᶜ_default_) using (_∈?_)
open Decidable _≟-ValueId_ renaming (_‼_default_ to _‼ᵛ_default_) hiding (_∈?_)
open PosixTime using (getPosixTime)

_/_ : Int → Int → Int
_/_ num den with (∣ den ∣ ℕ.≟ 0) | (λ proof -> _div_ num den {proof})
... | true  because _ | _      = 0ℤ
... | false because _ | result = result _


ℰ⟦_⟧ : Value → Environment → State → Int

𝒪⟦_⟧ : Observation → Environment → State → Bool

ℰ⟦ AvailableMoney a t ⟧ _ s = + ((a , t) ‼ᵃ accounts s default 0)
ℰ⟦ Constant x ⟧ _ _ = x
ℰ⟦ NegValue x ⟧ e s = - ℰ⟦ x ⟧ e s
ℰ⟦ AddValue x y ⟧ e s = ℰ⟦ x ⟧ e s + ℰ⟦ y ⟧ e s
ℰ⟦ SubValue x y ⟧ e s = ℰ⟦ x ⟧ e s - ℰ⟦ y ⟧ e s
ℰ⟦ MulValue x y ⟧ e s = ℰ⟦ x ⟧ e s * ℰ⟦ y ⟧ e s
ℰ⟦ DivValue x y ⟧ e s = ℰ⟦ x ⟧ e s / ℰ⟦ y ⟧ e s
ℰ⟦ ChoiceValue c ⟧ _ s = c ‼ᶜ choices s default 0ℤ
ℰ⟦ TimeIntervalStart ⟧ e _ = + getPosixTime (startTime (timeInterval e))
ℰ⟦ TimeIntervalEnd ⟧ e _ = + getPosixTime (endTime (timeInterval e))
ℰ⟦ UseValue v ⟧ _ s = v ‼ᵛ boundValues s default 0ℤ
ℰ⟦ Cond o x y ⟧ e s = if 𝒪⟦ o ⟧ e s then ℰ⟦ x ⟧ e s else ℰ⟦ y ⟧ e s

𝒪⟦ AndObs x y ⟧ e s = 𝒪⟦ x ⟧ e s ∧ 𝒪⟦ y ⟧ e s
𝒪⟦ OrObs x y ⟧ e s = 𝒪⟦ x ⟧ e s ∨ 𝒪⟦ y ⟧ e s
𝒪⟦ NotObs x ⟧ e s = not (𝒪⟦ x ⟧ e s)
𝒪⟦ ChoseSomething c ⟧  _ s = ⌊ c ∈? choices s ⌋
𝒪⟦ ValueGE y x ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≤? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueGT y x ⟧ e s = ⌊ ℰ⟦ x ⟧ e s <? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueLT x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s <? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueLE x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≤? ℰ⟦ y ⟧ e s ⌋
𝒪⟦ ValueEQ x y ⟧ e s = ⌊ ℰ⟦ x ⟧ e s ≟ ℰ⟦ y ⟧ e s ⌋
𝒪⟦ TrueObs ⟧ _ _ = true
𝒪⟦ FalseObs ⟧ _ _ = false
