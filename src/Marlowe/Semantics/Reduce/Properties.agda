module Marlowe.Semantics.Reduce.Properties where

open import Data.Integer using (∣_∣; +_)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; sum; filter; map)
open import Data.List.Relation.Unary.Any using (lookup; _─_; _∷=_; here; there)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂)
open import Function.Base using (case_of_; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)

open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Reduce

open import Primitives
open Decidable _≟-AccountId×Token_ renaming (_↑_ to _↑-AccountId×Token_)

open State using (accounts; boundValues; choices)
open Configuration

totalAmount : Configuration → ℕ
totalAmount c = accountsTotal (accounts (state c)) ℕ.+ paymentsTotal (payments c)

-- TODO: by token
⇀assetPreservation : ∀ {c₁ c₂} → (t : Token) → (c₁ ⇀ c₂) → totalAmount c₁ ≡ totalAmount c₂
⇀assetPreservation _ (CloseRefund {_} {_} {i}) = rearrange {x = i}
   where
     rearrange : ∀ { x a b : ℕ } → (x ℕ.+ a) ℕ.+ b ≡ a ℕ.+ (x ℕ.+ b)
     rearrange {x} {a} {b} =
       let p = sym (cong (ℕ._+ b) (+-comm a x))
           q = +-assoc a x b
        in trans p q
⇀assetPreservation _ (PayNonPositive _) = refl
⇀assetPreservation _ (PayNoAccount _ _) = refl
⇀assetPreservation _ (PayInternalTransfer {s} {e} {v} {aₛ} {aₜ} {t} {ps = ps} x p) =
  cong (ℕ._+ (paymentsTotal ps)) (constValue {a₁ = aₛ} {a₂ = aₜ} {abs = accounts s} {n = ∣ ℰ⟦ v ⟧ e s ∣})
⇀assetPreservation _ (PayExternal {s} {e} {v} {a} {t} {c} {ws} {ps} {p} o q) =
  let n = ∣ ℰ⟦ v ⟧ e s ∣ 
      m = proj₂ (lookup q)
      s₁ = cong (ℕ._+  paymentsTotal ((mkPayment a (mkParty p) t (m ℕ.⊓ n)) ∷ ps))
             (decreaseValue {a} {t} {abs = accounts s} {n = n} {p = q})
      s₂ = monusElim {a = accountsTotal (accounts s)} {b = paymentsTotal ps} {x = m ⊓ n}
  in trans (sym s₂) (sym s₁)
⇀assetPreservation _ (IfTrue _) = refl
⇀assetPreservation _ (IfFalse _) = refl
⇀assetPreservation _ (WhenTimeout _) = refl
⇀assetPreservation _ (LetShadow _ _) = refl
⇀assetPreservation _ (LetNoShadow _) = refl
⇀assetPreservation _ (AssertTrue _) = refl
⇀assetPreservation _ (AssertFalse _) = refl

