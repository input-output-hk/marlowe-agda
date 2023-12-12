module Marlowe.Semantics.Reduce.Properties where

open import Contrib.Data.Nat.Properties
open import Data.Integer using (∣_∣)
open import Data.List using (List; _∷_; []; _++_; sum; filter; map)
open import Data.List.Relation.Unary.Any using (lookup; _∷=_)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_; _$_; _|>_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)

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
open Environment
open TimeInterval
open PosixTime

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
totalAmount : Token → Configuration → ℕ
totalAmount t c = Σ-accounts t (accounts (state c)) + Σ-payments t (payments c)

⇀assetPreservation :
  ∀ {c₁ c₂ : Configuration}
  → (t : Token)
  → (c₁ ⇀ c₂)
  --------------------------------
  → totalAmount t c₁ ≡ totalAmount t c₂
⇀assetPreservation t* (CloseRefund {a} {t} {i}) = m+n+o≡n+[m+o] {m = projₜ t* ((a , t) , i)}
⇀assetPreservation _ (PayNonPositive _) = refl
⇀assetPreservation _ (PayNoAccount _ _) = refl
⇀assetPreservation t* (PayInternalTransfer {s} {e} {v} {aₛ} {aₜ} {t} {ps = ps} _ aₛ×t∈as) =
  cong (_+ Σ-payments t* ps) (sym pay-internal-transfer)
  where
    m = proj₂ (lookup aₛ×t∈as)
    n = ∣ ℰ⟦ v ⟧ e s ∣

    pay-internal-transfer :
      Σ-accounts t* (((aₜ , t) , m ⊓ n) ↑-update (aₛ×t∈as ∷= ((aₛ , t) , m ∸ n))) ≡ Σ-accounts t* (accounts s)
    pay-internal-transfer with (aₜ , t) ∈?-AccountId×Token (aₛ×t∈as ∷= ((aₛ , t) , m ∸ n))
    ... | yes aₜ×t∈as′ =
              trans
                (trans
                  (Σ-accounts-↑ (m ⊓ n) t* aₜ×t∈as′)
                  (trans
                    (+-comm (projₜ t* ((aₛ , t) , m ⊓ n)) (Σ-accounts t* (aₛ×t∈as ∷= ((aₛ , t) , m ∸ n))))
                    (cong (_+ (projₜ t* ((aₛ , t) , m ⊓ n))) (Σ-accounts-↓ n t* aₛ×t∈as))))
                (m∸n+n≡m (Σ-accounts-↓≤⊓ n t* aₛ×t∈as))
    ... | no aₜ×t∉as′ =
              trans
                (trans
                  (+-comm (projₜ t* ((aₜ , t) ,  m ⊓ n)) (Σ-accounts t* (aₛ×t∈as ∷= ((aₛ , t) , m ∸ n))))
                  (cong (_+ (projₜ t* ((aₛ , t) , m ⊓ n))) (Σ-accounts-↓ n t* aₛ×t∈as)))
                (m∸n+n≡m (Σ-accounts-↓≤⊓ n t* aₛ×t∈as))
⇀assetPreservation t* (PayExternal {s} {e} {v} {a} {t} {ps = ps} {p} _ a×t∈as) = sym $
  trans
    (cong (_+ (Σ-payments t* (a [ t , m ⊓ n ]↦ mkParty p ∷ ps))) (Σ-accounts-↓ n t* a×t∈as))
    (o≤m⇛m∸o+[o+n]≡m+n (Σ-accounts-↓≤⊓ n t* a×t∈as))
  where
    m = proj₂ (lookup a×t∈as)
    n = ∣ ℰ⟦ v ⟧ e s ∣
⇀assetPreservation _ (IfTrue _) = refl
⇀assetPreservation _ (IfFalse _) = refl
⇀assetPreservation _ (WhenTimeout _) = refl
⇀assetPreservation _ (LetShadow _ _) = refl
⇀assetPreservation _ (LetNoShadow _) = refl
⇀assetPreservation _ (AssertTrue _) = refl
⇀assetPreservation _ (AssertFalse _) = refl

-- Reducing a closed contract does not produce any warning
⇀⋆Close-is-safe :
  ∀ {c₂} {s₁ s₂} {e₁ e₂} {ws₁ ws₂} {ps₁ ps₂}
  → ⟪ Close , s₁ , e₁ , ws₁ , ps₁ ⟫ ⇀⋆ ⟪ c₂ , s₂ , e₂ , ws₂ , ps₂ ⟫
  → ws₁ ≡ ws₂
⇀⋆Close-is-safe ((⟪ Close , _ , _ , _ , _ ⟫) ∎) = refl
⇀⋆Close-is-safe ((⟪ Close , _ , _ , _ , _ ⟫) ⇀⟨ CloseRefund ⟩ x) rewrite ⇀⋆Close-is-safe x = refl

-- Close is a terminal contract
⇀⋆Close-is-terminal :
  ∀ {c₂} {s₁ s₂} {e₁ e₂} {ws₁ ws₂} {ps₁ ps₂}
  → ⟪ Close , s₁ , e₁ , ws₁ , ps₁ ⟫ ⇀⋆ ⟪ c₂ , s₂ , e₂ , ws₂ , ps₂ ⟫
  → c₂ ≡ Close
⇀⋆Close-is-terminal ((⟪ Close , _ , _ , _ , _ ⟫) ∎) = refl
⇀⋆Close-is-terminal ((⟪ Close , _ , _ , _ , _ ⟫) ⇀⟨ CloseRefund ⟩ x) rewrite ⇀⋆Close-is-terminal x = refl

↠-Close-is-terminal :
  ∀ {C D}
  → C ↠ D
  → contract C ≡ Close
  → contract D ≡ Close
↠-Close-is-terminal (Reduce-until-quiescent C⇀⋆D _) refl = ⇀⋆Close-is-terminal C⇀⋆D
↠-Close-is-terminal (Reduce-error C⇀⋆D _) refl = ⇀⋆Close-is-terminal C⇀⋆D

↠-Close-is-safe :
  ∀ {C D}
  → C ↠ D
  → contract C ≡ Close
  → warnings C ≡ warnings D
↠-Close-is-safe (Reduce-until-quiescent C⇀⋆D _) refl = ⇀⋆Close-is-safe C⇀⋆D
↠-Close-is-safe (Reduce-error C⇀⋆D _) refl = ⇀⋆Close-is-safe C⇀⋆D

⇀-env-not-modified :
  ∀ {C D}
  → C ⇀ D
  → (environment C) ≡ (environment D)
⇀-env-not-modified CloseRefund = refl
⇀-env-not-modified (PayNonPositive _) = refl
⇀-env-not-modified (PayNoAccount _ _) = refl
⇀-env-not-modified (PayInternalTransfer _ _) = refl
⇀-env-not-modified (PayExternal _ _) = refl
⇀-env-not-modified (IfTrue _) = refl
⇀-env-not-modified (IfFalse _) = refl
⇀-env-not-modified (WhenTimeout _) = refl
⇀-env-not-modified (LetShadow _ _) = refl
⇀-env-not-modified (LetNoShadow _) = refl
⇀-env-not-modified (AssertTrue _) = refl
⇀-env-not-modified (AssertFalse _) = refl

⇀⋆-env-not-modified :
  ∀ {C D}
  → C ⇀⋆ D
  → (environment C) ≡ (environment D)
⇀⋆-env-not-modified (_ ∎) = refl
⇀⋆-env-not-modified (_ ⇀⟨ x ⟩ y) rewrite ⇀-env-not-modified x = ⇀⋆-env-not-modified y

⇀-expiry : ∀ {C D}
  → C ⇀ D
  → expiry (contract D) ≤ expiry (contract C)
⇀-expiry CloseRefund = ≤-refl
⇀-expiry (PayNonPositive _) = ≤-refl
⇀-expiry (PayNoAccount _ _) = ≤-refl
⇀-expiry (PayInternalTransfer _ _) = ≤-refl
⇀-expiry (PayExternal _ _) = ≤-refl
⇀-expiry (IfTrue {c₁ = c₁} {c₂ = c₂} _) = m≤m⊔n (expiry c₁) (expiry c₂)
⇀-expiry (IfFalse {c₁ = c₁} {c₂ = c₂} _) = m≤n⊔m (expiry c₁) (expiry c₂)
⇀-expiry (WhenTimeout {t = t} {c = c} {cs = []} x) = m≤n⊔m t (expiry c)
⇀-expiry (WhenTimeout {s} {t} {tₛ} {Δₜ} {c} {ws} {ps} {(mkCase _ c₁) ∷ cs} x) =
  ≤-trans
    (⇀-expiry (WhenTimeout {s} {t} {tₛ} {Δₜ} {c} {ws} {ps} {cs} x))
    (m≤n⊔m (expiry c₁) (expiry (When cs (mkTimeout (mkPosixTime t)) c)))
⇀-expiry (LetShadow _ _) = ≤-refl
⇀-expiry (LetNoShadow _) = ≤-refl
⇀-expiry (AssertTrue _) = ≤-refl
⇀-expiry (AssertFalse _) = ≤-refl

⇀⋆-expiry : ∀ {C D}
  → C ⇀⋆ D
  → expiry (contract D) ≤ expiry (contract C)
⇀⋆-expiry (_ ∎) = ≤-refl
⇀⋆-expiry (_ ⇀⟨ x ⟩ y) = ≤-trans (⇀⋆-expiry y) (⇀-expiry x)

⇀⋆-reduce-after-timeout-closes-contract :
  ∀ {c s e ws ps D}
  → ⟪ c , s , e , ws , ps ⟫ ⇀⋆ D
  → Quiescent D
  → expiry c < getPosixTime (startTime (timeInterval e))
  → (contract D) ≡ Close
⇀⋆-reduce-after-timeout-closes-contract x close x₂ = refl
⇀⋆-reduce-after-timeout-closes-contract x (waiting {t} {tₛ} {Δₜ} {cs} {s} {c} x₁) x₂ rewrite ⇀⋆-env-not-modified x =
  contradiction
    (≤-trans
      (expiry-When t cs c)
      (⇀⋆-expiry x))
    (<⇒≱ (≤-trans
           (≤-stepsʳ (suc Δₜ) x₂)
           (≤-trans
             (≤-reflexive (+-suc tₛ Δₜ))
             x₁)))
  where
    expiry-When : ∀ t cs c → t ≤ expiry ( When cs (mkTimeout (mkPosixTime t)) c)
    expiry-When t [] c = m≤m⊔n t (expiry c)
    expiry-When t ((mkCase _ x) ∷ cs) c =
      ≤-trans
        (expiry-When t cs c)
        (m≤n⊔m (expiry x) (expiry (When cs (mkTimeout (mkPosixTime t)) c)))
