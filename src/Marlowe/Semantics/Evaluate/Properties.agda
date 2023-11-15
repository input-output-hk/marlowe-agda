module Marlowe.Semantics.Evaluate.Properties where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int)
open import Data.Bool using (_∧_; _∨_; if_then_else_; not)
open import Data.Integer using (-_; _+_; _-_; _*_; _≟_; _<?_; _≤?_; ∣_∣; 0ℤ; NonZero)
open import Data.Integer.Properties using (+-identityʳ; *-identityʳ; +-assoc)
open import Data.Nat as ℕ using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Integer using (0ℤ; 1ℤ; +_)
open import Relation.Nullary.Decidable using (⌊_⌋)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Marlowe.Language.Contract
open import Marlowe.Language.State
open import Marlowe.Semantics.Evaluate

0ᵥ : Value
0ᵥ = Constant 0ℤ

1ᵥ : Value
1ᵥ = Constant 1ℤ

AddValue-identityʳ : ∀ (e : Environment) → ∀ (s : State) → ∀ (n : Value) → ℰ⟦ AddValue n 0ᵥ ⟧ e s ≡ ℰ⟦ n ⟧ e s
AddValue-identityʳ e s n =
  begin
    ℰ⟦ AddValue n 0ᵥ ⟧ e s
    ≡⟨⟩
    ℰ⟦ n ⟧ e s + ℰ⟦ 0ᵥ ⟧ e s
    ≡⟨⟩
    ℰ⟦ n ⟧ e s + 0ℤ
    ≡⟨ +-identityʳ (ℰ⟦ n ⟧ e s) ⟩
    ℰ⟦ n ⟧ e s
  ∎

MulValue-identityʳ : ∀ (e : Environment) → ∀ (s : State) → ∀ (n : Value) → ℰ⟦ MulValue n 1ᵥ ⟧ e s ≡ ℰ⟦ n ⟧ e s
MulValue-identityʳ e s n =
  begin
    ℰ⟦ MulValue n 1ᵥ ⟧ e s
    ≡⟨⟩
    ℰ⟦ n ⟧ e s * ℰ⟦ 1ᵥ ⟧ e s
    ≡⟨⟩
    ℰ⟦ n ⟧ e s * 1ℤ
    ≡⟨ *-identityʳ (ℰ⟦ n ⟧ e s) ⟩
    ℰ⟦ n ⟧  e s
  ∎

AddValue-assoc : ∀ (e : Environment) → ∀ (s : State) → ∀ (m n p : Value) → ℰ⟦ AddValue (AddValue m n) p ⟧ e s ≡ ℰ⟦ AddValue m (AddValue n p) ⟧ e s
AddValue-assoc e s m n p =
  begin
    ℰ⟦ AddValue (AddValue m n) p ⟧ e s
    ≡⟨⟩
    ℰ⟦ AddValue m n ⟧ e s + ℰ⟦ p ⟧ e s
    ≡⟨⟩
    (ℰ⟦ m ⟧ e s + ℰ⟦ n ⟧ e s) + ℰ⟦ p ⟧ e s
    ≡⟨ +-assoc (ℰ⟦ m ⟧ e s) (ℰ⟦ n ⟧ e s) (ℰ⟦ p ⟧ e s) ⟩
    ℰ⟦ m ⟧ e s + (ℰ⟦ n ⟧ e s + ℰ⟦ p ⟧ e s)
    ≡⟨⟩
    ℰ⟦ m ⟧ e s + ℰ⟦ AddValue n p ⟧ e s
    ≡⟨⟩
    ℰ⟦ AddValue m (AddValue n p) ⟧ e s
  ∎
