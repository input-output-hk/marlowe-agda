module Marlowe.Semantics.Reduce.Properties where

open import Data.Integer using (∣_∣; +_)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (lookup; _∷=_)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)

open import Marlowe.Language.Contract
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Reduce

open import Primitives
open Decidable _≟-AccountId×Token_ renaming (_∈?_ to _∈?-AccountId×Token_)

open State using (accounts; boundValues; choices)
open Configuration

-- Quiescent configurations do not reduce
Quiescent¬⇀ :
  ∀ {c₁ c₂ : Configuration}
  → Quiescent c₁
  ---------------------------
  → ¬ (c₁ ⇀ c₂)
Quiescent¬⇀ close ()
Quiescent¬⇀ (waiting {t} {tₛ} {Δₜ} (x)) (WhenTimeout {_} {t} {tₛ} {Δₜ} y) =
  let ¬p = ≤⇒≯ (≤-trans y (m≤m+n tₛ Δₜ)) in ¬p x

-- If a configuration reduces, it is not quiescent
⇀¬Quiescent :
  ∀ {c₁ c₂ : Configuration}
  → c₁ ⇀ c₂
  ----------------
  → ¬ Quiescent c₁
⇀¬Quiescent c₁⇀c₂ q = Quiescent¬⇀ q c₁⇀c₂

-- A reduction step preserves assets
totalAmount : Configuration → ℕ
totalAmount c = Σ-accounts (accounts (state c)) + Σ-payments (payments c)

-- TODO: per Token
⇀assetPreservation :
  ∀ {c₁ c₂ : Configuration}
  → (c₁ ⇀ c₂)
  --------------------------------
  → totalAmount c₁ ≡ totalAmount c₂
⇀assetPreservation (CloseRefund {_} {_} {i = m}) = m+n+o≡n+[m+o] {m}
⇀assetPreservation (PayNonPositive _) = refl
⇀assetPreservation (PayNoAccount _ _) = refl
⇀assetPreservation (PayInternalTransfer {s} {e} {v} {aₛ} {aₜ} {t} {ps = ps} _ p) = go
  where
    aₛ×t = proj₁ (lookup p)
    m = proj₂ (lookup p)
    n = ∣ ℰ⟦ v ⟧ e s ∣
    a₁ = Σ-accounts-↓ {aₛ} {t} {accounts s} {n} p
    ≤-cond = ≤-trans
            (Σ-accounts-≤ {(aₛ , t)} {accounts s} {m ⊓ n} p)
            (Σ-accounts-↓≤ {(aₛ , t)} {accounts s} {n} p)
    pay-internal-transfer : Σ-accounts (accounts s)
         ≡ Σ-accounts (((aₜ , t) , m ⊓ n) ↑-update (p ∷= (proj₁ (lookup p) , m ∸ n)))
    pay-internal-transfer with (aₜ , t) ∈?-AccountId×Token (p ∷= (aₛ×t , m ∸ n))
    ... | yes q =
           let s₁ = trans (+-comm (m ⊓ n) (Σ-accounts (p ∷= (aₛ×t , m ∸ n)))) (cong (_+ m ⊓ n) a₁)
               a₂ = Σ-accounts-↑ {(aₜ , t)} {p ∷= (aₛ×t , m ∸ n)} {m ⊓ n} q
           in sym (trans (trans a₂ s₁)
                      (m∸n+n≡m {m = Σ-accounts (accounts s)} {n = m ⊓ n} ≤-cond))
    ... | no ¬q =
           let a₂ = Σ-accounts-∷ {m ⊓ n} {(aₜ , t)} {p ∷= (aₛ×t , m ∸ n)}
               s₁ = trans (trans a₂ (+-comm (m ⊓ n) (Σ-accounts (p ∷= (aₛ×t , m ∸ n))))) (cong (_+ m ⊓ n) a₁)
           in sym (trans s₁
                      (m∸n+n≡m {m = Σ-accounts (accounts s)} {n = m ⊓ n} ≤-cond))
    go = cong (_+ Σ-payments ps) pay-internal-transfer
⇀assetPreservation (PayExternal {s} {e} {v} {a} {t} {c} {ws} {ps} {p} _ q) =
  let n = ∣ ℰ⟦ v ⟧ e s ∣ 
      m = proj₂ (lookup q)
      p₁ = Σ-payments ((mkPayment a (mkParty p) t (m ⊓ n)) ∷ ps)
      a₁ = Σ-accounts-↓ {a} {t} {accounts s} {n} q
      s₁ = o≤m⇛m∸o+[o+n]≡m+n {Σ-accounts (accounts s)} {Σ-payments ps} {m ⊓ n}
             (≤-trans
               (Σ-accounts-≤ {(a , t)} {accounts s} {m ⊓ n} q)
               (Σ-accounts-↓≤ {(a , t)} {accounts s} {n} q))
  in sym (trans (cong (_+ p₁) a₁) s₁)
⇀assetPreservation (IfTrue _) = refl
⇀assetPreservation (IfFalse _) = refl
⇀assetPreservation (WhenTimeout _) = refl
⇀assetPreservation (LetShadow _ _) = refl
⇀assetPreservation (LetNoShadow _) = refl
⇀assetPreservation (AssertTrue _) = refl
⇀assetPreservation (AssertFalse _) = refl
