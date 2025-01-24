```agda
open import Marlowe.Abstract

module Marlowe.Semantics.Reduce (ma : MarloweAbstract) (open MarloweAbstract ma)
  where
```

This module contains the formalisation of small step reduction semantics for Marlowe.
The formalization was initially proposed by the Faustus team at University of Wyoming, see
Appendix A in "Developing Faustus: A Formally Verified Smart Contract Programming Language"

<!--
## Imports

```agda
open import Data.Bool using (if_then_else_; true; false)
open import Data.Bool.Properties using (_≟_; ¬-not)
open import Data.Integer using (ℤ; 0ℤ; _>_; _≤_; ∣_∣; _<?_; _≤?_)
import Data.Integer.Properties as ℤ
open import Data.List using (List; []; _∷_; [_]; lookup)
open import Data.Nat as ℕ using (ℕ; zero; suc; s≤s; _⊓_; _∸_; _+_; _<ᵇ_; _≤ᵇ_; _<_; _≥_)
open import Data.Nat.Properties using (1+n≰n; ≤-trans; +-identityʳ; +-comm; +-assoc; ≤⇒≯; m≤m+n; ≰⇒>; ≮⇒≥)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Class.Decidable
open import Prelude.AssocList
open import Prelude.Irrelevance
open import Prelude.InferenceRules
open import Data.List.Relation.Unary.First using (index)

open import Marlowe.Language ma
open import Marlowe.Semantics.Evaluate ma

open Environment using (timeInterval)
open State using (accounts; boundValues; choices)
open TimeInterval using (startTime)
```
-->
<!--
### Account updates

```agda
_↑-update_ : (AccountId × Token) × ℕ → AssocList (AccountId × Token) ℕ → AssocList (AccountId × Token) ℕ
(a , b) ↑-update abs with a ∈ᵐ? abs
... | yes p = p ∷= (proj₂ (lookup abs (index p)) + b)
... | no _ = (a , b) ∷ abs
```
-->
# Small-step semantics

## Reduce warnings

```agda
data ReduceWarning : Set where
  ReduceNonPositivePay  : AccountId → Payee → Token → ℤ → ReduceWarning
  ReducePartialPay      : AccountId → Payee → Token → ℕ → ℕ → ReduceWarning
  ReducePayNoAccount    : AccountId → Payee → Token → ℤ → ReduceWarning
  ReduceShadowing       : ValueId → ℤ → ℤ → ReduceWarning
  ReduceAssertionFailed : ReduceWarning
```

## Configuration

```agda
record Configuration : Set where
  constructor ⟪_,_,_,_,_⟫
  field contract    : Contract
        state       : State
        environment : Environment
        warnings    : List ReduceWarning
        payments    : List Payment

open Configuration
```

## Small-step reduction rules

```agda
private variable
   a aₛ aₜ    : AccountId
   t          : Token
   n tₛ tᵢ Δₜ : ℕ
   s          : State
   w          : ReduceWarning
   ws         : List ReduceWarning
   pₐ         : Party
   p          : Payee
   ps         : List Payment
   e          : Environment
   c c₁ c₂    : Contract
   cs         : List Case
   v          : Value
   vs         : List Value
   i          : ValueId
   o          : Observation
```
```agda
data _⇀_ : Configuration → Configuration → Set where
```
#### Reduction rules for `Close` contracts
```agda
  CloseRefund :
      ────────────────────────────────────────────────
      ⟪ Close
      , record s
          { accounts =
            ((a , t) , n) ∷ accounts s
          }
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ Close
      , s
      , e
      , ws
      , a [ t , n ]↦ mkParty (unAccountId a) ∷ ps
      ⟫
```
#### Reduction rules for `Pay` contracts
```agda
  PayNonPositive :
    ∙ ℰ⟦ v ⟧ e s ≤ 0ℤ
      ────────────────────────────────────────────────
      ⟪ Pay a p t v c , s , e , ws , ps ⟫ ⇀
      ⟪ c , s , e , ReduceNonPositivePay a p t (ℰ⟦ v ⟧ e s) ∷ ws , ps ⟫
```
```agda
  PayNoAccount :
    ∙ ℰ⟦ v ⟧ e s > 0ℤ
    ∙ (a , t) ∉ᵐ accounts s
      ────────────────────────────────────────────────
      ⟪ Pay a p t v c , s , e , ws , ps ⟫ ⇀
      ⟪ c , s , e , ReducePayNoAccount a p t (ℰ⟦ v ⟧ e s) ∷ ws , ps ⟫
```
```agda
  PayInternalTransfer :
    ∙ ℰ⟦ v ⟧ e s > 0ℤ
    → (aₛ×t∈as : (aₛ , t) ∈ᵐ accounts s) →
      ────────────────────────────────────────────────
      let
        m = proj₂ (lookup (accounts s) (index aₛ×t∈as))
        n = ∣ ℰ⟦ v ⟧ e s ∣
      in
      ⟪ Pay aₛ (mkAccount aₜ) t v c , s , e , ws , ps ⟫ ⇀
      ⟪ c
      , record s
          { accounts =
            ((aₜ , t) , (m ⊓ n)) ↑-update (aₛ×t∈as ∷= (m ∸ n))
          }
      , e
      , if (m <ᵇ n)
          then ReducePartialPay aₛ (mkAccount aₜ) t m n ∷ ws
          else ws
      , ps
      ⟫
```
```agda
  PayExternal :
    ∙ ℰ⟦ v ⟧ e s > 0ℤ
    → (a×t∈as : (a , t) ∈ᵐ accounts s) →
      ────────────────────────────────────────────────
      let
        m = proj₂ (lookup (accounts s) (index a×t∈as))
        n = ∣ ℰ⟦ v ⟧ e s ∣
      in
      ⟪ Pay a (mkParty pₐ) t v c , s , e , ws , ps ⟫ ⇀
      ⟪ c
      , record s
          { accounts =
            a×t∈as ∷= (m ∸ n)
          }
      , e
      , if (m <ᵇ n)
          then ReducePartialPay a (mkParty pₐ) t m n ∷ ws
          else ws
      , a [ t , m ⊓ n ]↦ mkParty pₐ ∷ ps
      ⟫
```
#### Reduction rules for `If` contracts
```agda
  IfTrue :
    ∙ 𝒪⟦ o ⟧ e s ≡ true
      ────────────────────────────────────────────────
      ⟪ If o c₁ c₂ , s , e , ws , ps ⟫ ⇀
      ⟪ c₁ , s , e , ws , ps ⟫
```
```agda
  IfFalse :
    ∙ 𝒪⟦ o ⟧ e s ≡ false
      ────────────────────────────────────────────────
      ⟪ If o c₁ c₂ , s , e , ws , ps ⟫ ⇀
      ⟪ c₂ , s , e , ws , ps ⟫
```
#### Reduction rules for `When` contracts
```agda
  WhenTimeout : let e = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) in
    ∙ tᵢ ℕ.≤ tₛ
      ────────────────────────────────────────────────
      ⟪ When cs (mkTimeout (mkPosixTime tᵢ)) c , s , e , ws , ps ⟫ ⇀
      ⟪ c , s , e , ws , ps ⟫
```
#### Reduction rules for `Let` contracts
```agda
  LetShadow :
      (i∈bs : i ∈ᵐ boundValues s) →
      ────────────────────────────────────────────────
      ⟪ Let i v c , s , e , ws , ps ⟫ ⇀
      ⟪ c
      , s
      , e
      , ReduceShadowing i (proj₂ (lookup (boundValues s) (index i∈bs))) (ℰ⟦ v ⟧ e s) ∷ ws
      , ps
      ⟫
```
```agda
  LetNoShadow :
    ∙ i ∉ᵐ boundValues s
      ────────────────────────────────────────────────
      ⟪ Let i v c , s , e , ws , ps ⟫ ⇀
      ⟪ c
      , record s
          { boundValues =
            (i , ℰ⟦ v ⟧ e s) ∷ boundValues s
          }
      , e
      , ws
      , ps
      ⟫
```
#### Reduction rules for `Assert` contracts
```agda
  AssertTrue :
    ∙ 𝒪⟦ o ⟧ e s ≡ true
      ────────────────────────────────────────────────
      ⟪ Assert o c , s , e , ws , ps ⟫ ⇀
      ⟪ c , s , e , ws , ps ⟫
```
```agda
  AssertFalse :
    ∙ 𝒪⟦ o ⟧ e s ≡ false
      ────────────────────────────────────────────────
      ⟪ Assert o c , s , e , ws , ps ⟫ ⇀
      ⟪ c , s , e , ReduceAssertionFailed ∷ ws , ps ⟫
```

### Reflexive and transitive closure

```agda
open import Prelude.Closures (_⇀_) renaming (_—↠_ to _⇀⋆_; _—→⟨_⟩_ to _⇀⟨_⟩_) public
```

### Quiescent

A contract that is either waiting for input or has been fully reduced is called
quiescent.

```agda
private variable
   ac : AssocList ChoiceId ℤ
   av : AssocList ValueId ℤ
   m  : PosixTime
```
```agda
data Quiescent : Configuration → Set where

  close :
      ───────────────────────
      Quiescent
        ⟪ Close
        , ⟨ [] , ac , av , m ⟩
        , e
        , ws
        , ps
        ⟫

  waiting :
    ∙ tₛ + Δₜ < tᵢ
      ─────────────────────────────
      Quiescent
        ⟪ When cs (mkTimeout (mkPosixTime tᵢ)) c
        , s
        , mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
        , ws
        , ps
        ⟫
```

### Ambiguous time interval



```agda
data AmbiguousTimeInterval : Configuration → Set where

  AmbiguousTimeIntervalError :
    ∙ tₛ < tᵢ
    ∙ tₛ + Δₜ ≥ tᵢ
      ────────────────────────────────────────────────
      AmbiguousTimeInterval
        ⟪ When cs (mkTimeout (mkPosixTime tᵢ)) c
        , s
        , mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
        , ws
        , ps
        ⟫
```

## Reducible

A configuration is reducible, if

* there is a reduction step or
* the configuration is quiescent or
* the time interval is ambiguous

```agda
private variable
  D : Configuration

data Reducible (C : Configuration) : Set where

  step :
    ∙ C ⇀ D
      ───────────
      Reducible C

  quiescent :
    ∙ Quiescent C
      ───────────
      Reducible C

  ambiguousTimeInterval :
    ∙ AmbiguousTimeInterval C
      ───────────────────────
      Reducible C
```

Every configuration is reducible:

```agda
progress : ∀ (C : Configuration) → Reducible C
progress
  ⟪ Close
  , ⟨ [] , _ , _ , _ ⟩
  , _
  , _
  , _
  ⟫ = quiescent close
progress
  ⟪ Close
  , ⟨ _ ∷ _ , _ , _ , _ ⟩
  , _
  , _
  , _
  ⟫ = step CloseRefund
progress
  ⟪ Pay a (mkAccount p) t v c
  , s@(⟨ as , _ , _ , _ ⟩)
  , e
  , _
  , _
  ⟫ with ℰ⟦ v ⟧ e s ≤? 0ℤ | (a , t) ∈ᵐ? as
... | yes v≤0 | _           = step (PayNonPositive v≤0)
... | no  v≰0 | yes a×t∈as = step (PayInternalTransfer (ℤ.≰⇒> v≰0) a×t∈as)
... | no  v≰0 | no ¬a×t∈as = step (PayNoAccount (ℤ.≰⇒> v≰0) λ x → ⊥⇒·⊥ (¬a×t∈as x))
progress
  ⟪ Pay a (mkParty p) t v _
  , s@(⟨ as , _ , _ , _ ⟩)
  , e
  , _
  , _
  ⟫ with ℰ⟦ v ⟧ e s ≤? 0ℤ | (a , t) ∈ᵐ? as
... | yes v≤0 | _           = step (PayNonPositive v≤0)
... | no  v≰0 | yes a×t∈as = step (PayExternal (ℤ.≰⇒> v≰0) a×t∈as)
... | no  v≰0 | no ¬a×t∈as = step (PayNoAccount (ℤ.≰⇒> v≰0) λ x → ⊥⇒·⊥ (¬a×t∈as x))
progress
  ⟪ If o c₁ c₂
  , s
  , e
  , _
  , _
  ⟫ with 𝒪⟦ o ⟧ e s ≟ true
... | yes o≡true = step (IfTrue o≡true)
... | no ¬o≡true = step (IfFalse (¬-not ¬o≡true))
progress
  ⟪ When cs (mkTimeout (mkPosixTime t)) c
  , _
  , mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
  , _
  , _
  ⟫ with (tₛ + Δₜ) ℕ.<? t | t ℕ.≤? tₛ
... | yes tₑ<t | _        = quiescent (waiting tₑ<t)
... | _        | yes t≤tₛ = step (WhenTimeout t≤tₛ)
... | no ¬tₑ<t | no ¬t≤tₛ  = ambiguousTimeInterval (AmbiguousTimeIntervalError (≰⇒> ¬t≤tₛ) (≮⇒≥ ¬tₑ<t))
progress
  ⟪ Let i v c , s@(⟨ _ , _ , vs , _ ⟩)
  , e
  , ws
  , ps
  ⟫ with i ∈ᵐ? vs
... | yes i∈vs = step (LetShadow i∈vs)
... | no ¬a∈abs = step (LetNoShadow λ x → ⊥⇒·⊥ (¬a∈abs x))
progress
  ⟪ Assert o c
  , s
  , e
  , _
  , _
  ⟫ with 𝒪⟦ o ⟧ e s ≟ true
... | yes o≡true = step (AssertTrue o≡true)
... | no ¬o≡true = step (AssertFalse (¬-not ¬o≡true))
```

## Evaluator

```agda
{-# TERMINATING #-} -- TODO: use sized types instead
⇀-eval :
  ∀ (C : Configuration)
  → Σ[ D ∈ Configuration ] ((C ⇀⋆ D) × (Quiescent D ⊎ AmbiguousTimeInterval D))
⇀-eval C with progress C
... | quiescent q = C , (C ∎) , inj₁ q
... | ambiguousTimeInterval a = C , (C ∎) , inj₂ a
... | step {D} C⇀D with ⇀-eval D
...      | E , D⇀⋆E , q⊎a = E , (C ⇀⟨ C⇀D ⟩ D⇀⋆E) , q⊎a
```

### Example

The reduction steps of a contract until it is quiescent can be generated by Agda using
`C-c C-n`.

```agda
private

  module _ (party : Party) (token : Token)
    where

    accountId : AccountId
    accountId = mkAccountId party

    config₂ : Configuration
    config₂ =
      ⟪ If TrueObs Close Close
      , ⟨ [ (accountId , token ) , 5 ] , [] , [] , mkPosixTime 0 ⟩
      , mkEnvironment (mkInterval (mkPosixTime 0) 5)
      , []
      , []
      ⟫

    config₁ : Configuration
    config₁ =
      ⟪ Close
      , ⟨ [ ( accountId , token ) , 5 ] , [] , [] , mkPosixTime 0 ⟩
      , mkEnvironment (mkInterval (mkPosixTime 0) 5)
      , []
      , []
      ⟫

    config₀ : Configuration
    config₀ =
      ⟪ Close
      , ⟨ [] , [] , [] , mkPosixTime 0 ⟩
      , mkEnvironment (mkInterval (mkPosixTime 0) 5)
      , []
      , [ accountId [ token , 5 ]↦ mkParty (unAccountId accountId) ]
      ⟫

    _ = ⇀-eval config₂
        ≡ ( config₀
          , (config₂ ⇀⟨ IfTrue refl ⟩ config₁ ⇀⟨ CloseRefund ⟩ config₀ ∎)
          , inj₁ close
          )
```
