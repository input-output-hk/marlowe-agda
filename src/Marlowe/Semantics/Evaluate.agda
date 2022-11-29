

module Marlowe.Semantics.Evaluate where


open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int)
open import Data.Bool using (_∧_; _∨_; if_then_else_; not)
open import Data.Integer using (-_; _+_; _-_; _*_; _≟_; _<?_; _≤?_; ∣_∣; 0ℤ; NonZero)
open import Data.Integer.DivMod using (_div_)
open import Data.Nat as ℕ using ()
open import Marlowe.Language.Contract
open import Marlowe.Language.State
open import Primitives
open import Relation.Nullary using (_because_)
open import Relation.Nullary.Decidable using (⌊_⌋)


divide : Int → Int → Int
divide num den with (∣ den ∣ ℕ.≟ 0) | (λ proof -> _div_ num den {proof})
... | true  because _ | _      = 0ℤ
... | false because _ | result = result _


evaluate : Environment → State → Value → Int

observe : Environment → State → Observation → Bool

evaluate _ s (AvailableMoney a t) = record {fst = a; snd = t} lookup (State.accounts s) default 0ℤ
evaluate _ _ (Constant x) = x
evaluate e s (NegValue x) = - evaluate e s x
evaluate e s (AddValue x y) = evaluate e s x + evaluate e s y
evaluate e s (SubValue x y) = evaluate e s x - evaluate e s y
evaluate e s (MulValue x y) = evaluate e s x * evaluate e s y
evaluate e s (DivValue x y) = divide (evaluate e s x) (evaluate e s y)
evaluate _ s (ChoiceValue c) = c lookup (State.choices s) default 0ℤ
evaluate e _ TimeIntervalStart = unPosixTime (Pair.fst (Environment.timeInterval e))
evaluate e _ TimeIntervalEnd = unPosixTime (Pair.snd (Environment.timeInterval e))
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
