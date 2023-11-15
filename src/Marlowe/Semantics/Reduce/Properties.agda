module Marlowe.Semantics.Reduce.Properties where

open import Data.Integer using (∣_∣; +_)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (lookup)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; proj₁; proj₂)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)

open import Marlowe.Language.Contract
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Reduce

open State using (accounts; boundValues; choices)
open Configuration

totalAmount : Configuration → ℕ
totalAmount c = accountsTotal (accounts (state c)) + paymentsTotal (payments c)

-- TODO: per Token
⇀assetPreservation : ∀ {c₁ c₂} → (c₁ ⇀ c₂) → totalAmount c₁ ≡ totalAmount c₂
⇀assetPreservation (CloseRefund {_} {_} {i}) = rearrange {x = i}
  where
    rearrange : ∀ { x a b : ℕ } → (x + a) + b ≡ a + (x + b)
    rearrange {x} {a} {b} =
      let s₁ = sym (cong (_+ b) (+-comm a x))
          s₂ = +-assoc a x b
      in trans s₁ s₂
⇀assetPreservation (PayNonPositive _) = refl
⇀assetPreservation (PayNoAccount _ _) = refl
⇀assetPreservation (PayInternalTransfer {s} {e} {v} {aₛ} {aₜ} {t} {ps = ps} _ p) =
  cong (_+ (paymentsTotal ps)) (constValue {a₁ = aₛ} {a₂ = aₜ} {abs = accounts s} {n = ∣ ℰ⟦ v ⟧ e s ∣})
⇀assetPreservation (PayExternal {s} {e} {v} {a} {t} {c} {ws} {ps} {p} _ q) =
  let n = ∣ ℰ⟦ v ⟧ e s ∣ 
      m = proj₂ (lookup q)
      s₁ = cong (_+  paymentsTotal ((mkPayment a (mkParty p) t (m ⊓ n)) ∷ ps))
             (decreaseValue {a} {t} {abs = accounts s} {n = n} {p = q})
      s₂ = monusElim {a = accountsTotal (accounts s)} {b = paymentsTotal ps} {x = m ⊓ n}
  in sym (trans s₁ s₂)
⇀assetPreservation (IfTrue _) = refl
⇀assetPreservation (IfFalse _) = refl
⇀assetPreservation (WhenTimeout _) = refl
⇀assetPreservation (LetShadow _ _) = refl
⇀assetPreservation (LetNoShadow _) = refl
⇀assetPreservation (AssertTrue _) = refl
⇀assetPreservation (AssertFalse _) = refl
