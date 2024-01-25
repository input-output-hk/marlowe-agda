---
title: Marlowe.Semantics.Reduce.Properties
layout: page
---

```
open import Relation.Binary using (DecidableEquality)

module Marlowe.Semantics.Reduce.Properties
  {Party : Set} (_≟-Party_ : DecidableEquality Party)
  {Token : Set} (_≟-Token_ : DecidableEquality Token)
  where
```

## Imports

```
open import Contrib.Data.Nat.Properties
open import Data.Bool.Properties using (not-¬)
open import Data.Integer using (∣_∣)
open import Data.List using (List; _∷_; []; _++_; sum; filter; map)
open import Data.List.Relation.Unary.Any using (lookup; _∷=_; here; there)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Function.Base using (_∘_; _$_; _|>_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)

open import Marlowe.Language
open Entities-Parameterized-by-Party {Party}
open Entities-Parameterized-by-Token {Token}
open Equality _≟-Party_ _≟-Token_

open import Marlowe.Language.Properties {Party} _≟-Token_
open import Marlowe.Semantics.Evaluate _≟-Party_ _≟-Token_
open import Marlowe.Semantics.Reduce _≟-Party_ _≟-Token_

open import Contrib.Data.List.AssocList
open Decidable (≡-dec _≟-AccountId_ _≟-Token_) renaming (_∈?_ to _∈?-AccountId×Token_)

open Entities-Parameterized-by-Token.State
open Configuration
open Environment
open TimeInterval
open PosixTime
```

## Quiescent

Quiescent configurations do not reduce

```
Quiescent¬⇀ : ∀ {C₁ C₂}
  → Quiescent C₁
    ------------
  → ¬ (C₁ ⇀ C₂)
Quiescent¬⇀ close ()
Quiescent¬⇀ (waiting {t} {tₛ} {Δₜ} (x)) (WhenTimeout {_} {t} {tₛ} {Δₜ} y) =
  let ¬p = ≤⇒≯ (≤-trans y (m≤m+n tₛ Δₜ)) in ¬p x
```

If a configuration reduces, it is not quiescent

```
⇀¬Quiescent : ∀ {C₁ C₂}
  → C₁ ⇀ C₂
    --------------
  → ¬ Quiescent C₁
⇀¬Quiescent C₁⇀C₂ q = Quiescent¬⇀ q C₁⇀C₂
```

## Asset preservation

A reduction step preserves assets

```
totalAmount : Token → Configuration → ℕ
totalAmount t C = Σ-accounts t (accounts (state C)) + Σ-payments t (payments C)

⇀assetPreservation :
  ∀ {C₁ C₂ : Configuration}
  → (t : Token)
  → (C₁ ⇀ C₂)
  --------------------------------
  → totalAmount t C₁ ≡ totalAmount t C₂
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
⇀assetPreservation _ (LetShadow _) = refl
⇀assetPreservation _ (LetNoShadow _) = refl
⇀assetPreservation _ (AssertTrue _) = refl
⇀assetPreservation _ (AssertFalse _) = refl
```

```
⇀⋆assetPreservation :
  ∀ {C₁ C₂ : Configuration}
  → (t : Token)
  → (C₁ ⇀⋆ C₂)
  --------------------------------
  → totalAmount t C₁ ≡ totalAmount t C₂
⇀⋆assetPreservation t (_ ∎) = refl
⇀⋆assetPreservation t (_ ⇀⟨ x ⟩ x₁) rewrite ⇀assetPreservation t x = ⇀⋆assetPreservation t x₁
```

## Closing is safe

Reducing a closed contract does not produce any warning

```
⇀⋆Close-is-safe :
  ∀ {c₂} {s₁ s₂} {e₁ e₂} {ws₁ ws₂} {ps₁ ps₂}
  → ⟪ Close , s₁ , e₁ , ws₁ , ps₁ ⟫ ⇀⋆ ⟪ c₂ , s₂ , e₂ , ws₂ , ps₂ ⟫
  → ws₁ ≡ ws₂
⇀⋆Close-is-safe ((⟪ Close , _ , _ , _ , _ ⟫) ∎) = refl
⇀⋆Close-is-safe ((⟪ Close , _ , _ , _ , _ ⟫) ⇀⟨ CloseRefund ⟩ x) rewrite ⇀⋆Close-is-safe x = refl
```

Close is a terminal contract

```
⇀⋆Close-is-terminal :
  ∀ {c₂} {s₁ s₂} {e₁ e₂} {ws₁ ws₂} {ps₁ ps₂}
  → ⟪ Close , s₁ , e₁ , ws₁ , ps₁ ⟫ ⇀⋆ ⟪ c₂ , s₂ , e₂ , ws₂ , ps₂ ⟫
  → c₂ ≡ Close
⇀⋆Close-is-terminal ((⟪ Close , _ , _ , _ , _ ⟫) ∎) = refl
⇀⋆Close-is-terminal ((⟪ Close , _ , _ , _ , _ ⟫) ⇀⟨ CloseRefund ⟩ x) rewrite ⇀⋆Close-is-terminal x = refl
```

```
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
⇀-env-not-modified (LetShadow _) = refl
⇀-env-not-modified (LetNoShadow _) = refl
⇀-env-not-modified (AssertTrue _) = refl
⇀-env-not-modified (AssertFalse _) = refl
```

## Finite contracts

```
⇀⋆-env-not-modified :
  ∀ {C D}
  → C ⇀⋆ D
  → (environment C) ≡ (environment D)
⇀⋆-env-not-modified (_ ∎) = refl
⇀⋆-env-not-modified (_ ⇀⟨ x ⟩ y) rewrite ⇀-env-not-modified x = ⇀⋆-env-not-modified y
```

```
⇀-maxTimeout : ∀ {C D}
  → C ⇀ D
  → maxTimeout (contract D) ≤ maxTimeout (contract C)
⇀-maxTimeout CloseRefund = ≤-refl
⇀-maxTimeout (PayNonPositive _) = ≤-refl
⇀-maxTimeout (PayNoAccount _ _) = ≤-refl
⇀-maxTimeout (PayInternalTransfer _ _) = ≤-refl
⇀-maxTimeout (PayExternal _ _) = ≤-refl
⇀-maxTimeout (IfTrue {c₁ = c₁} {c₂ = c₂} _) = m≤m⊔n (maxTimeout c₁) (maxTimeout c₂)
⇀-maxTimeout (IfFalse {c₁ = c₁} {c₂ = c₂} _) = m≤n⊔m (maxTimeout c₁) (maxTimeout c₂)
⇀-maxTimeout (WhenTimeout {t = t} {c = c} {cs = []} x) = m≤n⊔m t (maxTimeout c)
⇀-maxTimeout (WhenTimeout {s} {t} {tₛ} {Δₜ} {c} {ws} {ps} {(mkCase _ c₁) ∷ cs} x) =
  ≤-trans
    (⇀-maxTimeout (WhenTimeout {s} {t} {tₛ} {Δₜ} {c} {ws} {ps} {cs} x))
    (m≤n⊔m (maxTimeout c₁) (maxTimeout (When cs (mkTimeout (mkPosixTime t)) c)))
⇀-maxTimeout (LetShadow _) = ≤-refl
⇀-maxTimeout (LetNoShadow _) = ≤-refl
⇀-maxTimeout (AssertTrue _) = ≤-refl
⇀-maxTimeout (AssertFalse _) = ≤-refl
```

```
⇀⋆-maxTimeout : ∀ {C D}
  → C ⇀⋆ D
  → maxTimeout (contract D) ≤ maxTimeout (contract C)
⇀⋆-maxTimeout (_ ∎) = ≤-refl
⇀⋆-maxTimeout (_ ⇀⟨ x ⟩ y) = ≤-trans (⇀⋆-maxTimeout y) (⇀-maxTimeout x)
```

## Timed-out transaction closes contract

```
⇀⋆-after-timeout-closes-contract : ∀ {C D}
  → C ⇀⋆ D
  → Quiescent D
  → maxTimeout (contract C) < getPosixTime (startTime (timeInterval (environment C)))
  → (contract D) ≡ Close
⇀⋆-after-timeout-closes-contract _ close _ = refl
⇀⋆-after-timeout-closes-contract x (waiting {t} {tₛ} {Δₜ} {cs} {s} {c} x₁) x₂ rewrite ⇀⋆-env-not-modified x =
  contradiction
    (≤-trans
      (timeout≤maxTimeout t cs c)
      (⇀⋆-maxTimeout x))
    (<⇒≱ (≤-trans
           (m≤n⇒m≤n+o (suc Δₜ) x₂)
           (≤-trans
             (≤-reflexive (+-suc tₛ Δₜ))
             x₁)))
  where
    timeout≤maxTimeout : ∀ t cs c → t ≤ maxTimeout (When cs (mkTimeout (mkPosixTime t)) c)
    timeout≤maxTimeout t [] c = m≤m⊔n t (maxTimeout c)
    timeout≤maxTimeout t ((mkCase _ x) ∷ cs) c =
      ≤-trans
        (timeout≤maxTimeout t cs c)
        (m≤n⊔m (maxTimeout x) (maxTimeout (When cs (mkTimeout (mkPosixTime t)) c)))
```
