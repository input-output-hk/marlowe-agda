module Marlowe.Semantics.Operate where

open import Agda.Builtin.Int using (Int)
open import Data.Bool as 𝔹 using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Integer as ℤ using (∣_∣; +_)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecSetoid using () renaming (_∈?_ to _∈?-List_)
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there; lookup)
open import Data.List.Relation.Unary.Any.Properties using (map⁻)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ; suc; zero; _<_; _<?_; _≟_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂)
import Data.String as String
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Reduce

open import Contrib.Data.List.Membership using (∈-∷)
open import Contrib.Data.List.AssocList renaming (_∈_ to _∈′_)
open Decidable _≟-AccountId×Token_  renaming (_‼_default_ to _‼-AccountId×Token_default_; _↑_ to _↑-AccountId×Token_) hiding (_∈?_)
open Decidable _≟-ChoiceId_ renaming (_‼_default_ to _‼-ChoiceId_default_;  _↑_ to _↑-ChoiceId_) using (_∈?_)
open Decidable _≟-ValueId_ renaming (_‼_ to _‼_ValueId_; _‼_default_ to _‼-ValueId_default_; _∈?_ to _∈-ValueId?_; _↑_ to _↑-ValueId_)

open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

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
    → (interval-end e) ℕ.< t
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
    → (q : Quiescent D)
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
    ----------------------------------------------------
    → ( waiting {cs = cs} {t = tₒ} {c = c} {s = s} {e = e} {ws = ws} {ps = ps} tₑ<tₒ
      , NormalInput (IDeposit a p t n)
      ) ⇒ D

  Choice : ∀ {cₐ c i n s bs ws ps cs tₒ e D}
    → (mkCase (Choice i bs) cₐ) ∈ cs
    → n inBounds bs ≡ true
    → (tₑ<tₒ : interval-end e < tₒ)
    → (q : Quiescent D)
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
    ----------------------------------------------------
    → ( waiting {cs = cs} {t = tₒ} {c = c} {s = s} {e = e} {ws = ws} {ps = ps} tₑ<tₒ
      , NormalInput (IChoice i n)
      ) ⇒ D

  Notify : ∀ {cₐ c s o cs tₒ e ws ps D}
    → (mkCase (Notify o) cₐ) ∈ cs
    → 𝒪⟦ o ⟧ e s ≡ true
    → (tₑ<tₒ : interval-end e < tₒ)
    → (q : Quiescent D)
    → ( ⟪ cₐ
        , s
        , e
        , ws
        , ps
        ⟫
      ) ⇀⋆ D
    --------------------------------------------
    → ( waiting {cs = cs} {t = tₒ} {c = c} {s = s} {e = e} {ws = ws} {ps = ps} tₑ<tₒ
      , NormalInput INotify
      ) ⇒ D

{-# TERMINATING #-} -- TODO: replace recursion
⇒-eval :
  ∀ {C : Configuration}
  → (w : Waiting C)
  → (i : Input)
  → (Σ[ D ∈ Configuration ] (((w , i) ⇒ D) × (Quiescent D))) ⊎ TransactionError
⇒-eval (waiting {[]} _) _ = inj₂ TEApplyNoMatchError

-- Deposit

⇒-eval
  (waiting {mkCase (Deposit a₁ p₁ t₁ v) cₐ ∷ cs} {_} {c} {s} {e} {ws} {ps} tₑ<t)
  x@(NormalInput (IDeposit a₂ p₂ t₂ n))
  with a₁ ≟-AccountId a₂ | p₁ ≟-Party p₂ | t₁ ≟-Token t₂ | ℰ⟦ v ⟧ e s  ℤ.≟ + n |
    eval ⟪ cₐ , record s { accounts = ((a₁ , t₁) , n) ↑-update (accounts s) } , e , ws , ps ⟫
... | yes refl | yes refl | yes refl | yes ℰ⟦v⟧≡+n | (D , Reduce-until-quiescent C⇀⋆D  q) = inj₁ (D , Deposit (here refl) ℰ⟦v⟧≡+n tₑ<t q C⇀⋆D , q)
... | yes _    | yes _    | yes _    | yes _       | (D , Ambiguous-time-interval _ _)    = inj₂ TEAmbiguousTimeIntervalError
... | _        | _        | _        | _           | _
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} tₑ<t)
      x
... | inj₁ (D , (Deposit x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Deposit (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

⇒-eval
  (waiting {mkCase (Deposit a p t v) cₐ ∷ cs} {_} {c} {s} {e} {ws} {ps} tₑ<t)
  x@(NormalInput (IChoice i n))
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} {s = s} tₑ<t)
      x
... | inj₁ (D , (Choice x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Choice (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

⇒-eval
  (waiting {mkCase (Deposit a p t v) cₐ ∷ cs} {_} {c} {s} {e} {ws} {ps} tₑ<t)
  x@(NormalInput INotify)
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} {s = s} tₑ<t)
      x
... | inj₁ (D , (Notify x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Notify (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

-- Choice

⇒-eval
  (waiting {mkCase (Choice i₁ b₁) cₐ ∷ cs} {t} {c} {s} {e} {ws} {ps} tₑ<t)
  (NormalInput (IChoice i₂ n₂))
  with i₁ ≟-ChoiceId i₂ | n₂ inBounds b₁ 𝔹.≟ true |
    eval ⟪ cₐ , record s { choices = (i₁ , unChosenNum n₂) ↑-ChoiceId (choices s) } , e , ws , ps ⟫
... | yes refl | yes p | (D , Reduce-until-quiescent C⇀⋆D q) = inj₁ (D , Choice (here refl) p tₑ<t q C⇀⋆D , q)
... | yes _    | yes _ | (_ , Ambiguous-time-interval _ _)    = inj₂ TEAmbiguousTimeIntervalError
... | _        | _     | _
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} {s = s} tₑ<t)
      (NormalInput (IChoice i₂ n₂))
... | inj₁ (D , (Choice x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Choice (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

⇒-eval
  (waiting {mkCase (Choice i₁ b₁) cₐ ∷ cs} {t} {c} {s} {e} {ws} {ps} tₑ<t)
  x@(NormalInput (IDeposit a₂ p₂ t₂ n))
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} {s = s} tₑ<t)
      x
... | inj₁ (D , (Deposit x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Deposit (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

⇒-eval
  (waiting {mkCase (Choice i₁ b₁) cₐ ∷ cs} {t} {c} {s} {e} {ws} {ps} tₑ<t)
  x@(NormalInput INotify)
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} {s = s} tₑ<t)
      x
... | inj₁ (D , (Notify x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Notify (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

-- Notify

⇒-eval
  (waiting {mkCase (Notify o) cₐ ∷ cs} {t} {c} {s} {e} {ws} {ps} tₑ<t)
  (NormalInput INotify)
  with 𝒪⟦ o ⟧ e s 𝔹.≟ true |
    eval ⟪ cₐ , s , e , ws , ps ⟫
... | yes o≡true | (D , Reduce-until-quiescent C⇀⋆D q) = inj₁ (D , Notify (here refl) o≡true tₑ<t q C⇀⋆D , q)
... | yes _      | (_ , Ambiguous-time-interval _ _)    = inj₂ TEAmbiguousTimeIntervalError
... | no _       | _
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} tₑ<t)
      (NormalInput INotify)
... | inj₁ (D , (Notify x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Notify (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

⇒-eval
  (waiting {mkCase (Notify o) cₐ ∷ cs} {t} {c} {s} {e} {ws} {ps} tₑ<t)
  x@(NormalInput (IDeposit a₂ p₂ t₂ n))
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} tₑ<t)
      x
... | inj₁ (D , (Deposit x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Deposit (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e

⇒-eval
  (waiting {mkCase (Notify o) cₐ ∷ cs} {t} {c} {s} {e} {ws} {ps} tₑ<t)
  x@(NormalInput (IChoice i n))
  with
    ⇒-eval
      (waiting {cs = cs} {c = c} {s = s} tₑ<t)
      x
... | inj₁ (D , (Choice x x₁ x₂ x₃ x₄) , q) = inj₁ (D , (Choice (∈-∷ x) x₁ x₂ x₃ x₄ , q))
... | inj₂ e = inj₂ e


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

  apply-inputs :
    ∀ {i D s cs t c sc e ws ps ws′ ps′}
    → (tₑ<t : (interval-end e) ℕ.< t)
    → (waiting {cs = cs} {t = t} {c = c} {s = sc} {e = e} {ws = ws} {ps = ps} tₑ<t , i) ⇒ D
    → (contract D , state D) ⇓
      ⟦ ws′
      , ps′
      , s
      ⟧
    -------------------------------------------
    → (When cs (mkTimeout (mkPosixTime t)) c , sc) ⇓
      ⟦ ws′ ++ convertReduceWarnings (warnings D)
      , ps′ ++ payments D
      , s
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
⇓-eval Close s@(⟨ [] , _ , _ , _ ⟩) [] = inj₁ (⟦ [] , [] , s ⟧ , done refl)

⇓-eval
  (When cases (mkTimeout (mkPosixTime t)) _) s ((mkTransactionInput i@(mkInterval (mkPosixTime tₛ) Δₜ) _) ∷ is) with (tₛ ℕ.+ Δₜ) <? t
... | no t≤tₑ
    with eval ⟪ When cases (mkTimeout (mkPosixTime t)) _ , s , mkEnvironment i , [] , [] ⟫
...    | _ , Ambiguous-time-interval _ _ = inj₂ TEAmbiguousTimeIntervalError
...    | D , Reduce-until-quiescent C×i⇒D ¬q
    with ⇓-eval (contract D) (state D) is
...    | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) =
           inj₁ (⟦ ws ++ convertReduceWarnings (warnings D)
                 , ps ++ payments D
                 , s
                 ⟧
                 , reduce-until-quiescent refl refl C×i⇒D ¬q d×s×is⇓r
                )
...    | inj₂ e = inj₂ e

⇓-eval
  (When cases (mkTimeout (mkPosixTime t)) c) s ((mkTransactionInput i@(mkInterval (mkPosixTime tₛ) Δₜ) (ts ∷ tss)) ∷ is)
    | yes tₑ<t
    with ⇒-eval (waiting  {cs = cases} {t = t} {c = c} {s = s} {e = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)} {ws = []} {ps = []} tₑ<t) ts -- TODO: fixInterval
...    | inj₂ _ = inj₂ TEUselessTransaction
...    | inj₁ (D , C×i⇒D , _)
    with ⇓-eval (contract D) (state D) is
...    | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) =
           inj₁ (⟦ ws ++ convertReduceWarnings (warnings D)
                 , ps ++ payments D
                 , s
                 ⟧
                 , apply-inputs tₑ<t C×i⇒D d×s×is⇓r
                )
...    | inj₂ e = inj₂ e

⇓-eval
  (When cases (mkTimeout (mkPosixTime t)) c) s ((mkTransactionInput i@(mkInterval (mkPosixTime tₛ) Δₜ) []) ∷ is)
    | yes tₑ<t
    with eval ⟪ When cases (mkTimeout (mkPosixTime t)) _ , s , mkEnvironment i , [] , [] ⟫
...    | _ , Ambiguous-time-interval _ _ = inj₂ TEAmbiguousTimeIntervalError
...    | D , Reduce-until-quiescent C×i⇒D ¬q
    with ⇓-eval (contract D) (state D) is
...    | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) =
           inj₁ (⟦ ws ++ convertReduceWarnings (warnings D)
                 , ps ++ payments D
                 , s
                 ⟧
                 , reduce-until-quiescent refl refl C×i⇒D ¬q d×s×is⇓r
                )
...    | inj₂ e = inj₂ e

⇓-eval c s []
    with eval ⟪ c , s , mkEnvironment (mkInterval (mkPosixTime 0) 0) , [] , [] ⟫
... | _ , Ambiguous-time-interval _ _ = inj₂ TEAmbiguousTimeIntervalError
... | D , Reduce-until-quiescent C×i⇒D q
    with ⇓-eval (contract D) (state D) []
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) =
      inj₁ (⟦ ws ++ convertReduceWarnings (warnings D)
            , ps ++ payments D
            , s
            ⟧
            , reduce-until-quiescent refl refl C×i⇒D q d×s×is⇓r
           )
... | inj₂ e = inj₂ e
⇓-eval c s ((mkTransactionInput i _) ∷ is)
    with eval ⟪ c , s , mkEnvironment i , [] , [] ⟫
... | _ , Ambiguous-time-interval _ _ = inj₂ TEAmbiguousTimeIntervalError
... | D , Reduce-until-quiescent C×i⇒D q
    with ⇓-eval (contract D) (state D) is
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) =
      inj₁ (⟦ ws ++ convertReduceWarnings (warnings D)
            , ps ++ payments D
            , s
            ⟧
            , reduce-until-quiescent refl refl C×i⇒D q d×s×is⇓r
           )
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
      (apply-inputs {i = NormalInput (IDeposit a₁ p₂ t 1)} (s≤s (s≤s (s≤s z≤n)))
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
