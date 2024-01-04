module Marlowe.Semantics.Operate where

open import Agda.Builtin.Int using (Int)
open import Data.Bool as 𝔹 using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Integer as ℤ using (∣_∣; +_)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecSetoid using () renaming (_∈?_ to _∈?-List_)
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there; lookup; any?)
open import Data.List.Relation.Unary.Any.Properties -- using (map⁻)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ; suc; zero; _<_; _<ᵇ_; _<?_; _≟_; z≤n; s≤s; _+_; _⊔_; _∸_; _≥_)
open import Data.Nat.Properties using (≰⇒>; ≮⇒≥; ≤-reflexive; ≤-trans)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂)
import Data.String as String
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_ ;id)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.Consequences

open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Reduce

open import Contrib.Data.List.AssocList renaming (_∈_ to _∈′_)
open Decidable _≟-AccountId×Token_  renaming (_‼_default_ to _‼-AccountId×Token_default_; _↑_ to _↑-AccountId×Token_) hiding (_∈?_)
open Decidable _≟-ChoiceId_ renaming (_‼_default_ to _‼-ChoiceId_default_;  _↑_ to _↑-ChoiceId_) using (_∈?_)
open Decidable _≟-ValueId_ renaming (_‼_ to _‼_ValueId_; _‼_default_ to _‼-ValueId_default_; _∈?_ to _∈-ValueId?_; _↑_ to _↑-ValueId_)
open import Relation.Binary using (Decidable; DecidableEquality; WeaklyDecidable)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no; ¬_)


open Configuration
open State
open PosixTime
open TransactionInput

convertReduceWarnings : List ReduceWarning -> List TransactionWarning
convertReduceWarnings = map convertReduceWarning
  where
    convertReduceWarning : ReduceWarning → TransactionWarning
    convertReduceWarning (ReduceNonPositivePay a p t v) = TransactionNonPositivePay a p t v
    convertReduceWarning (ReducePartialPay a p t v e) = TransactionPartialPay a p t v e
    convertReduceWarning (ReduceShadowing i o n) = TransactionShadowing i o n
    convertReduceWarning ReduceAssertionFailed = TransactionAssertionFailed

data Waiting : Configuration → Set where

  waiting : ∀ {cs t c s e ws ps}
    → (interval-end e) < t
    -----------------------------------------------
    → Waiting
        ⟪ When cs (mkTimeout (mkPosixTime t)) c
        , s
        , e
        , ws
        , ps
        ⟫

data _⇒_ : {C : Configuration} → Waiting C × Input → Configuration → Set where

  Deposit : ∀ {a p t v n cₐ e s ws ps cs c tₒ D}
    → (mkCase (Deposit a p t v) cₐ) ∈ cs
    → ℰ⟦ v ⟧ e s ≡ + n
    → (tₑ<tₒ : interval-end e < tₒ)
    → Quiescent D
    → ( ⟪ cₐ
        , record s
            { accounts =
              ((a , t) , n) ↑-update (accounts s)
            }
        , e
        , ws
        , ps
        ⟫
      ) ⇀⋆ D
    -------------------------------------------------
    → ( waiting {cs} {tₒ} {c} {s} {e} {ws} {ps} tₑ<tₒ
      , NormalInput (IDeposit a p t n)
      ) ⇒ D

  Choice : ∀ {cₐ c i n s bs ws ps cs tₒ e D}
    → (mkCase (Choice i bs) cₐ) ∈ cs
    → n inBounds bs ≡ true
    → (tₑ<tₒ : interval-end e < tₒ)
    → Quiescent D
    → ( ⟪ cₐ
        , record s
            { choices =
              (i , unChosenNum n) ↑-ChoiceId (choices s)
            }
        , e
        , ws
        , ps
        ⟫
      ) ⇀⋆ D
    -------------------------------------------------
    → ( waiting {cs} {tₒ} {c} {s} {e} {ws} {ps} tₑ<tₒ
      , NormalInput (IChoice i n)
      ) ⇒ D

  Notify : ∀ {cₐ c s o cs tₒ e ws ps D}
    → (mkCase (Notify o) cₐ) ∈ cs
    → 𝒪⟦ o ⟧ e s ≡ true
    → (tₑ<tₒ : interval-end e < tₒ)
    → Quiescent D
    → ( ⟪ cₐ
        , s
        , e
        , ws
        , ps
        ⟫
      ) ⇀⋆ D
    -------------------------------------------------
    → ( waiting {cs} {tₒ} {c} {s} {e} {ws} {ps} tₑ<tₒ
      , NormalInput INotify
      ) ⇒ D


data _↦_ {s : State} {e : Environment} : InputContent → Action → Set where

  deposit-input : ∀ {a p t v n}
    → ℰ⟦ v ⟧ e s ≡ + n
    → IDeposit a p t n ↦ Deposit a p t v

  choice-input : ∀ {i n bs}
    → n inBounds bs ≡ true
    → IChoice i n ↦ Choice i bs

  notify-input : ∀ {o}
    → 𝒪⟦ o ⟧ e s ≡ true
    → INotify ↦ Notify o

applicable? : ∀ {s : State} {e : Environment} → (i : InputContent) → (a : Action) → Maybe (_↦_ {s} {e} i a)
applicable? {s} {e} (IDeposit a₁ p₁ t₁ n) (Deposit a₂ p₂ t₂ v)
  with a₁ ≟-AccountId a₂ | p₁ ≟-Party p₂ | t₁ ≟-Token t₂ | ℰ⟦ v ⟧ e s  ℤ.≟ + n
... | yes refl | yes refl | yes refl | yes p = just (deposit-input {_} {_} {a₁} {p₁} {t₁} {v} {n} p)
... | _        | _        | _        | _     = nothing
applicable? (IDeposit _ _ _ _) (Choice _ _ ) = nothing
applicable? (IDeposit _ _ _ _) (Notify _) = nothing
applicable? (IChoice _ _ ) (Deposit _ _ _ _ ) = nothing
applicable? (IChoice i₁ n) (Choice i₂ b)
  with i₁ ≟-ChoiceId i₂ | n inBounds b 𝔹.≟ true
... | yes refl | yes p = (just (choice-input {_} {_} {i₁} {n} {b} p))
... | _        | _     = nothing
applicable? (IChoice _ _) (Notify _) = nothing
applicable? INotify (Deposit _ _ _ _) = nothing
applicable? INotify (Choice _ _) = nothing
applicable? {s} {e} INotify (Notify o)
  with 𝒪⟦ o ⟧ e s 𝔹.≟ true
... | yes p = just (notify-input {_} {_} {o = o} p)
... | no _  = nothing

-- Evaluator for mid-step semantics

{-# TERMINATING #-} -- TODO: use sized types instead
⇒-eval :
  ∀ {C : Configuration}
  → (w : Waiting C)
  → (i : Input)
  → (Σ[ D ∈ Configuration ] ((w , i) ⇒ D)) ⊎ TransactionError
⇒-eval {⟪ When [] (mkTimeout (mkPosixTime tₒ)) c , s , e , ws , ps ⟫} (waiting tₑ<t) (NormalInput ic) = inj₂ TEApplyNoMatchError

⇒-eval (waiting {mkCase a cₐ ∷ cs} {t} {c} {s} {e} {ws} {ps} tₑ<t) (NormalInput ic)
  with applicable? {s} {e} ic a

-- here
⇒-eval (waiting {mkCase _ cₐ ∷ cs} {_} {_} {s} {e} {ws} {ps} tₑ<t) (NormalInput ic) | just (deposit-input {a} {p} {t} {_} {n} ℰ⟦v⟧≡+n)
  with ⇀-eval ⟪ cₐ , record s { accounts = ((a , t) , n) ↑-update (accounts s) } , e , ws , ps ⟫
... | D , C⇀⋆D , inj₁ q = inj₁ (D , Deposit (here refl) ℰ⟦v⟧≡+n tₑ<t q C⇀⋆D)
... | _ , _    , inj₂ _ = inj₂ TEAmbiguousTimeIntervalError
⇒-eval (waiting {mkCase _ cₐ ∷ cs} {_} {_} {s} {e} {ws} {ps} tₑ<t) (NormalInput ic) | just (choice-input {i} {n} {bs} p)
  with ⇀-eval ⟪ cₐ , record s { choices = (i , unChosenNum n) ↑-ChoiceId (choices s) } , e , ws , ps ⟫
... | D , C⇀⋆D , inj₁ q = inj₁ (D , Choice (here refl) p tₑ<t q C⇀⋆D)
... | _ , _    , inj₂ q = inj₂ TEAmbiguousTimeIntervalError
⇒-eval (waiting {mkCase _ cₐ ∷ cs} {_} {_} {s} {e} {ws} {ps} tₑ<t) (NormalInput ic) | just (notify-input {o} o≡true)
  with ⇀-eval ⟪ cₐ , s , e , ws , ps ⟫
... | D , C⇀⋆D , inj₁ q = inj₁ (D , Notify {s = s} {o = o} {e = e} (here refl) o≡true tₑ<t q C⇀⋆D)
... | _ , _    , inj₂ _ = inj₂ TEAmbiguousTimeIntervalError

-- there
⇒-eval (waiting {(_ ∷ cs)} {_} {c} tₑ<t) i@(NormalInput (IDeposit x x₁ x₂ x₃)) | nothing
  with ⇒-eval (waiting {cs} {_} {c} tₑ<t) i
... | inj₁ (D , (Deposit x x₁ x₂ x₃ x₄)) = inj₁ (D , (Deposit (there x) x₁ x₂ x₃ x₄))
... | inj₂ e = inj₂ e
⇒-eval (waiting {(_ ∷ cs)} {_} {c} {s} tₑ<t) i@(NormalInput (IChoice x x₁)) | nothing
  with ⇒-eval (waiting {cs} {_} {c} {s} tₑ<t) i
... | inj₁ (D , (Choice x x₁ x₂ x₃ x₄)) = inj₁ (D , (Choice (there x) x₁ x₂ x₃ x₄))
... | inj₂ e = inj₂ e
⇒-eval (waiting {(_ ∷ cs)} {_} {c} tₑ<t) i@(NormalInput INotify) | nothing
  with ⇒-eval (waiting {cs} {_} {c} tₑ<t) i
... | inj₁ (D , (Notify x x₁ x₂ x₃ x₄)) = inj₁ (D , (Notify (there x) x₁ x₂ x₃ x₄))
... | inj₂ e = inj₂ e


data _↝_ : Configuration → Configuration → Set where

  trim-interval : ∀ {c as cs bs tₘ tₛ Δₜ ws ps }
    → (tₛ + Δₜ) ≥ tₘ
    → ⟪ c
      , ⟨ as , cs , bs , mkPosixTime tₘ ⟩
      , mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
      , ws
      , ps
      ⟫
      ↝
      ⟪ c
      , ⟨ as , cs , bs , mkPosixTime (tₛ ⊔ tₘ) ⟩
      , mkEnvironment (mkInterval (mkPosixTime (tₛ ⊔ tₘ)) (Δₜ ∸ (tₘ ∸ tₛ)))
      , ws
      , ps
      ⟫

data FixInterval (B : Configuration) : Set where

  trim : ∀ {C}
    → B ↝ C
      -------------
    → FixInterval B

  error :
    interval-end (environment B) < getPosixTime (minTime (state B))
    → FixInterval B


fixInterval : ∀ (B : Configuration) → FixInterval B
fixInterval ⟪ _ , ⟨ _ , _ , _ , mkPosixTime tₘ ⟩ , mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) , _ , _ ⟫ with tₛ + Δₜ <? tₘ
... | yes p = error p
... | no p = trim (trim-interval (≮⇒≥ p))

record Result : Set where
  constructor ⟦_,_,_⟧
  field
    warnings : List TransactionWarning
    payments : List Payment
    state : State

data _⇓_ : Contract × State → Result → Set where

  reduce-until-quiescent :
    ∀ {C D ws ps s}
    → warnings C ≡ []
    → payments C ≡ []
    → C ⇀⋆ D
    → Quiescent D
    → (contract D , state D) ⇓
      ⟦ ws
      , ps
      , s
      ⟧
    -------------------------------------------
    → (contract C , state C) ⇓
      ⟦ ws ++ convertReduceWarnings (warnings D)
      , ps ++ payments D
      , s
      ⟧

  apply-input :
    ∀ {i cs t c s e ws ps C D ws′ ps′ s′}
    → (tₑ<t : interval-end (environment C) < t)
    → ⟪ When cs (mkTimeout (mkPosixTime t)) c , s , e , ws , ps ⟫ ↝ C
    → (waiting {cs} {t} {c} {state C} {environment C} {ws} {ps} tₑ<t , i) ⇒ D
    → (contract D , state D) ⇓
      ⟦ ws′
      , ps′
      , s′
      ⟧
    -------------------------------------------
    → (When cs (mkTimeout (mkPosixTime t)) c , s) ⇓
      ⟦ ws′ ++ convertReduceWarnings (warnings D)
      , ps′ ++ payments D
      , s′
      ⟧

  done :
    ∀ {s}
    → accounts s ≡ []
    -----------------
    → (Close , s) ⇓
      ⟦ []
      , []
      , s
      ⟧



{-# TERMINATING #-} -- TODO: use sized types instead
⇓-eval :
  ∀ (c : Contract)
  → (s : State)
  → List TransactionInput
  → (Σ[ r ∈ Result ] (c , s) ⇓ r) ⊎ TransactionError

-- Close
⇓-eval Close s@(⟨ [] , _ , _ , _ ⟩) [] = inj₁ (⟦ [] , [] , s ⟧ , done refl)

-- When
⇓-eval
  (When cs (mkTimeout (mkPosixTime t)) c) s@(⟨ _ , _ , _ , mkPosixTime tₘ ⟩) ((mkTransactionInput i@(mkInterval (mkPosixTime tₛ) Δₜ) _) ∷ is)
    with fixInterval ⟪ When cs (mkTimeout (mkPosixTime t)) c , s , mkEnvironment i , [] , [] ⟫
... | error _ = inj₂ (TEIntervalError (IntervalInPastError (mkPosixTime tₘ) i))
... | trim {C} B↝C
    with interval-end (environment C) <? t
... | no t≤tₑ
    with ⇀-eval ⟪ When cs (mkTimeout (mkPosixTime t)) c , s , mkEnvironment i , [] , [] ⟫
... | _ , _ , inj₂ _ = inj₂ TEAmbiguousTimeIntervalError
... | D , C×i⇒D , inj₁ q
    with ⇓-eval (contract D) (state D) is
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) = inj₁ (⟦ ws ++ convertReduceWarnings (warnings D) , ps ++ payments D , s ⟧ , reduce-until-quiescent refl refl C×i⇒D q d×s×is⇓r)
... | inj₂ e = inj₂ e

⇓-eval
  (When cs (mkTimeout (mkPosixTime t)) c) s ((mkTransactionInput i@(mkInterval (mkPosixTime tₛ) Δₜ) []) ∷ is)
    | trim B↝C | yes tₑ<t
    with ⇀-eval ⟪ When cs (mkTimeout (mkPosixTime t)) _ , s , mkEnvironment i , [] , [] ⟫
... | _ , _ , inj₂ _ = inj₂ TEAmbiguousTimeIntervalError
... | D , C×i⇒D , inj₁ q
    with ⇓-eval (contract D) (state D) is
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) = inj₁ (⟦ ws ++ convertReduceWarnings (warnings D) , ps ++ payments D , s ⟧ , reduce-until-quiescent refl refl C×i⇒D q d×s×is⇓r)
... | inj₂ e = inj₂ e

⇓-eval
  (When cs (mkTimeout (mkPosixTime t)) c) (⟨ as , css , bs , mkPosixTime tₘ ⟩) ((mkTransactionInput i@(mkInterval (mkPosixTime tₛ) Δₜ) (ts ∷ tss)) ∷ is)
    | trim {C} B↝C | yes tₑ<t
    with ⇒-eval (waiting {cs} {t} {c} {state C} {environment C} {[]} {[]} tₑ<t) ts
... | inj₂ _ = inj₂ TEUselessTransaction
... | inj₁ (D , C×i⇒D)
    with ⇓-eval (contract D) (state D) is
... | inj₁ (⟦ ws , ps , s′ ⟧ , d×s×is⇓r) = inj₁ (⟦ ws ++ convertReduceWarnings (warnings D) , ps ++ payments D , s′ ⟧ , apply-input {ts} {cs} {t} {c} {_} {e = mkEnvironment i} {[]} {[]} tₑ<t B↝C C×i⇒D d×s×is⇓r)
... | inj₂ e = inj₂ e

-- Otherwise
⇓-eval c s []
    with ⇀-eval ⟪ c , s , mkEnvironment (mkInterval (mkPosixTime 0) 0) , [] , [] ⟫
... | _ , _ , inj₂ _ = inj₂ TEAmbiguousTimeIntervalError
... | D , C×i⇒D , inj₁ q
    with ⇓-eval (contract D) (state D) []
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) = inj₁ (⟦ ws ++ convertReduceWarnings (warnings D) , ps ++ payments D , s ⟧ , reduce-until-quiescent refl refl C×i⇒D q d×s×is⇓r)
... | inj₂ e = inj₂ e

⇓-eval c s ((mkTransactionInput i _) ∷ is)
    with ⇀-eval ⟪ c , s , mkEnvironment i , [] , [] ⟫
... | _ , _ , inj₂ _ = inj₂ TEAmbiguousTimeIntervalError
... | D , C×i⇒D , inj₁ q
    with ⇓-eval (contract D) (state D) is
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) = inj₁ (⟦ ws ++ convertReduceWarnings (warnings D) , ps ++ payments D , s ⟧ , reduce-until-quiescent refl refl C×i⇒D q d×s×is⇓r)
... | inj₂ e = inj₂ e

private

  tₒ : PosixTime
  tₒ = mkPosixTime 100

  p₁ : Party
  p₁ = Role (mkByteString "role1")

  p₂ : Party
  p₂ = Role (mkByteString "role2")

  a₁ : AccountId
  a₁ = mkAccountId p₁

  a₂ : AccountId
  a₂ = mkAccountId p₂

  t : Token
  t = mkToken (mkByteString "") (mkByteString "")

  v : Value
  v = Constant (+ 1)

  d : Contract
  d = When ([ mkCase (Deposit a₁ p₂ t v) Close ]) (mkTimeout tₒ) Close

  c : Contract
  c = Assert FalseObs d

  s : State
  s = emptyState (mkPosixTime 0)

  i : TransactionInput
  i = mkTransactionInput (mkInterval (mkPosixTime 0) 10) [ NormalInput (IDeposit a₁ p₂ t 1) ]

  e : Environment
  e = mkEnvironment (mkInterval (mkPosixTime 0) 2)

  reduction-steps :
    (c , s)
    ⇓ ⟦ [ TransactionAssertionFailed ]
      , [ a₁ [ t , 1 ]↦ mkParty p₁ ]
      , s
      ⟧
  reduction-steps =
    reduce-until-quiescent refl refl
      (⟪ c , s , e , [] , [] ⟫ ⇀⟨ AssertFalse refl ⟩ (⟪ d , s , e , [ ReduceAssertionFailed ] , [] ⟫ ∎))
      (waiting (s≤s (s≤s (s≤s z≤n))))
      (apply-input {i = NormalInput (IDeposit a₁ p₂ t 1)} (s≤s (s≤s (s≤s z≤n))) (trim-interval z≤n)
        (Deposit (here refl) refl (s≤s (s≤s (s≤s z≤n))) close
          (⟪ Close , ⟨ [((a₁ , t) , 1)] , [] , [] , minTime s ⟩ , e , []  , [] ⟫
                 ⇀⟨ CloseRefund ⟩ (⟪ Close , ⟨ [] , [] , [] , (minTime s) ⟩ , e , [] , [ a₁ [ t , 1 ]↦ mkParty p₁ ] ⟫) ∎))
        (done refl))

  _ = ⇓-eval c s (i ∷ []) ≡
       inj₁ (
         ⟦ [ TransactionAssertionFailed ]
         , [ a₁ [ t , 1 ]↦ mkParty p₁ ]
         , s
         ⟧ , reduction-steps)
