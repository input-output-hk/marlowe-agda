
module Marlowe.Semantics.Evaluate where


open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int)
open import Data.Bool using (_∧_; _∨_; if_then_else_; not)
open import Data.Integer using (-_; _+_; _-_; _*_; _≟_; _<?_; _≤?_; ∣_∣; 0ℤ; NonZero)
open import Data.Integer.DivMod using (_div_)
open import Data.Integer.Properties using (+-identityʳ;*-identityʳ;+-assoc)
open import Data.Maybe using (fromMaybe)
open import Data.Nat as ℕ using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Integer using (0ℤ; 1ℤ; +_)
open import Marlowe.Language.Contract
open import Marlowe.Language.State
open import Primitives
import Primitives as P
open P.Decidable _eqAccountIdTokenDec_ using (_‼_)
open import Relation.Nullary using (_because_)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
import Relation.Nullary using (Dec; yes; no)


divide : Int → Int → Int
divide num den with (∣ den ∣ ℕ.≟ 0) | (λ proof -> _div_ num den {proof})
... | true  because _ | _      = 0ℤ
... | false because _ | result = result _


evaluate : Environment → State → Value → Int

observe : Environment → State → Observation → Bool

evaluate _ s (AvailableMoney a t) = fromMaybe 0ℤ ((a , t) ‼ (State.accounts s))
evaluate _ _ (Constant x) = x
evaluate e s (NegValue x) = - evaluate e s x
evaluate e s (AddValue x y) = evaluate e s x + evaluate e s y
evaluate e s (SubValue x y) = evaluate e s x - evaluate e s y
evaluate e s (MulValue x y) = evaluate e s x * evaluate e s y
evaluate e s (DivValue x y) = divide (evaluate e s x) (evaluate e s y)
evaluate _ s (ChoiceValue c) = c lookup (State.choices s) default 0ℤ
evaluate e _ TimeIntervalStart = PosixTime.getPosixTime (proj₁ (Environment.timeInterval e))
evaluate e _ TimeIntervalEnd = PosixTime.getPosixTime (proj₂ (Environment.timeInterval e))
evaluate _ s (UseValue v) = v lookup (State.boundValues s) default 0ℤ
evaluate e s (Cond o x y) = if observe e s o then evaluate e s x else evaluate e s y

observe e s (AndObs x y) = observe e s x ∧ observe e s y
observe e s (OrObs x y) = observe e s x ∨ observe e s y
observe e s (NotObs x) = not (observe e s x)
observe _ s (ChoseSomething c) = c member (State.choices s)
observe e s (ValueGE y x) = ⌊ evaluate e s x ≤? evaluate e s y ⌋
observe e s (ValueGT y x) = ⌊ evaluate e s x <? evaluate e s y ⌋
observe e s (ValueLT x y) = ⌊ evaluate e s x <? evaluate e s y ⌋
observe e s (ValueLE x y) = ⌊ evaluate e s x ≤? evaluate e s y ⌋
observe e s (ValueEQ x y) = ⌊ evaluate e s x ≟ evaluate e s y ⌋
observe _ _ TrueObs = true
observe _ _ FalseObs = false


zero : Value
zero = Constant 0ℤ

one : Value
one = Constant 1ℤ

AddValue-identityʳ : ∀ (e : Environment) → ∀ (s : State) → ∀ (n : Value) → evaluate e s (AddValue n zero) ≡ evaluate e s n
AddValue-identityʳ e s n =
  begin
    evaluate e s (AddValue n zero)
    ≡⟨⟩
    evaluate e s n + evaluate e s zero
    ≡⟨⟩
    evaluate e s n + 0ℤ
    ≡⟨ +-identityʳ (evaluate e s n) ⟩
    evaluate e s n
  ∎

MulValue-identityʳ : ∀ (e : Environment) → ∀ (s : State) → ∀ (n : Value) → evaluate e s (MulValue n one) ≡ evaluate e s n
MulValue-identityʳ e s n =
  begin
    evaluate e s (MulValue n one)
    ≡⟨⟩
    evaluate e s n * evaluate e s one
    ≡⟨⟩
    evaluate e s n * 1ℤ
    ≡⟨ *-identityʳ (evaluate e s n) ⟩
    evaluate e s n
  ∎

AddValue-assoc : ∀ (e : Environment) → ∀ (s : State) → ∀ (m n p : Value) → evaluate e s (AddValue (AddValue m n) p) ≡ evaluate e s (AddValue m (AddValue n p))
AddValue-assoc e s m n p =
  begin
    evaluate e s (AddValue (AddValue m n) p)
    ≡⟨⟩
    evaluate e s (AddValue m n) + evaluate e s p
    ≡⟨⟩
    (evaluate e s m + evaluate e s n) + evaluate e s p
    ≡⟨ +-assoc (evaluate e s m) (evaluate e s n) (evaluate e s p) ⟩
    evaluate e s m + (evaluate e s n + evaluate e s p)
    ≡⟨⟩
    evaluate e s m + evaluate e s (AddValue n p)
    ≡⟨⟩
    evaluate e s (AddValue m (AddValue n p))
  ∎
