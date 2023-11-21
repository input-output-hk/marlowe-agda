module Marlowe.Semantics.Reduce.Properties where

open import Contrib.Data.Nat.Properties
open import Data.Integer using (∣_∣; +_)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (lookup; _∷=_)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_; _$_; _|>_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)

open import Marlowe.Language.Contract
open import Marlowe.Language.State
open import Marlowe.Language.State.Properties
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Reduce

open import Contrib.Data.List.AssocList
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

⇀assetPreservation :
  ∀ {c₁ c₂ : Configuration}
  → (c₁ ⇀ c₂)
  --------------------------------
  → totalAmount c₁ ≡ totalAmount c₂
⇀assetPreservation (CloseRefund {i = m}) = m+n+o≡n+[m+o] {m}
⇀assetPreservation (PayNonPositive _) = refl
⇀assetPreservation (PayNoAccount _ _) = refl
⇀assetPreservation (PayInternalTransfer {s} {e} {v} {_} {aₜ} {t} {ps = ps} _ aₛ×t∈as) =
  cong (_+ Σ-payments ps) (sym pay-internal-transfer)
  where
    m = proj₂ (lookup aₛ×t∈as)
    n = ∣ ℰ⟦ v ⟧ e s ∣

    pay-internal-transfer :
      Σ-accounts (((aₜ , t) , m ⊓ n) ↑-update (aₛ×t∈as ∷= (proj₁ (lookup aₛ×t∈as) , m ∸ n))) ≡ Σ-accounts (accounts s)
    pay-internal-transfer with (aₜ , t) ∈?-AccountId×Token (aₛ×t∈as ∷= (proj₁ (lookup aₛ×t∈as) , m ∸ n))
    ... | yes aₜ×t∈as′ =
              trans
                (trans
                  (Σ-accounts-↑ (m ⊓ n) aₜ×t∈as′)
                  (trans (+-comm (m ⊓ n)
                    (Σ-accounts (aₛ×t∈as ∷= (proj₁ (lookup aₛ×t∈as) , m ∸ n))))
                    (cong (_+ m ⊓ n) (Σ-accounts-↓ n aₛ×t∈as))))
                (m∸n+n≡m (Σ-accounts-↓≤⊓ n aₛ×t∈as))
    ... | no aₜ×t∉as′ =
              trans
                (trans
                  (+-comm (m ⊓ n) (Σ-accounts (aₛ×t∈as ∷= (proj₁ (lookup aₛ×t∈as) , m ∸ n))))
                  (cong (_+ m ⊓ n) (Σ-accounts-↓ n aₛ×t∈as)))
                (m∸n+n≡m (Σ-accounts-↓≤⊓ n aₛ×t∈as))
⇀assetPreservation (PayExternal {s} {e} {v} {a} {t} {ps = ps} {p} _ a×t∈as) = sym $
  trans
    (cong (_+ (Σ-payments ((mkPayment a (mkParty p) t (m ⊓ n)) ∷ ps))) (Σ-accounts-↓ n a×t∈as))
    (o≤m⇛m∸o+[o+n]≡m+n (Σ-accounts-↓≤⊓ n a×t∈as))
  where
    m = proj₂ (lookup a×t∈as)
    n = ∣ ℰ⟦ v ⟧ e s ∣
⇀assetPreservation (IfTrue _) = refl
⇀assetPreservation (IfFalse _) = refl
⇀assetPreservation (WhenTimeout _) = refl
⇀assetPreservation (LetShadow _ _) = refl
⇀assetPreservation (LetNoShadow _) = refl
⇀assetPreservation (AssertTrue _) = refl
⇀assetPreservation (AssertFalse _) = refl
