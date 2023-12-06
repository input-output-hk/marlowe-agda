module Marlowe.Semantics.Operate where

open import Agda.Builtin.Int using (Int)
open import Data.Bool as 𝔹 using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Integer using (∣_∣; +_)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecSetoid using () renaming (_∈?_ to _∈?-List_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ; suc; zero; _<_; _<?_; _≟_; z≤n; s≤s)
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

open import Contrib.Data.List.AssocList hiding (_∈_)
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

data _⇒_ : Configuration × TransactionInput → Configuration → Set where

  Deposit :
    ∀ {a p t v n cₐ e s ws ps cs c tₒ is D}
    → (mkCase (Deposit a p t v) cₐ) ∈ cs
    → ∣ ℰ⟦ v ⟧ e s ∣ ≡ n
    → interval-end e < tₒ
    → ( ⟪ cₐ
        , record s
            { accounts =
              ((a , t) , n) ↑-update (accounts s)
            }
        , e
        , ws
        , ps
        ⟫
      ) ↠ D
    ----------------------------------------------------
    → ( ⟪ When cs (mkTimeout (mkPosixTime tₒ)) c
        , s
        , e
        , ws
        , ps
        ⟫
      , record is
          { inputs =
              NormalInput (IDeposit a p t n) ∷ inputs is
          }
      ) ⇒ D

  Choice :
    ∀ {cₐ c i n s is bs ws ps cs tₒ e D}
    → (mkCase (Choice i bs) cₐ) ∈ cs
    → n inBounds bs ≡ true
    → interval-end e < tₒ
    → ( ⟪ cₐ
        , record s
            { choices =
              (i , unChosenNum n) ↑-ChoiceId (choices s)
            }
        , e
        , ws
        , ps
        ⟫
      ) ↠ D
    ----------------------------------------------------
    → ( ⟪ When cs (mkTimeout (mkPosixTime tₒ)) c
        , s
        , e
        , ws
        , ps
        ⟫
      , record is
          { inputs =
            NormalInput (IChoice i n) ∷ inputs is
          }
      ) ⇒ D

  Notify :
    ∀ {cₐ c is s o cs tₒ e ws ps D}
    → (mkCase (Notify o) cₐ) ∈ cs
    → 𝒪⟦ o ⟧ e s ≡ true
    → interval-end e < tₒ
    → ( ⟪ cₐ
        , s
        , e
        , ws
        , ps
        ⟫
      ) ↠ D
    --------------------------------------------
    → ( ⟪ When cs (mkTimeout (mkPosixTime tₒ)) c
        , s
        , e
        , ws
        , ps
        ⟫
      , record is
          { inputs =
            NormalInput INotify ∷ inputs is
          }
      ) ⇒ D


∷-preserves-∈ :
  ∀ {A : Set} {x : A} {a : A} {as : List A}
  → x ∈ as
  --------------
  → x ∈ (a ∷ as)
∷-preserves-∈ (here refl) = there (here refl)
∷-preserves-∈ (there x) = there (∷-preserves-∈ x)

case∷-preserves-⇒ :
  ∀ { cs t c s e ws ps i case D}
  → (( ⟪ When cs t c , s , e , ws , ps ⟫ , i) ⇒ D)
  → (( ⟪ When (case ∷ cs) t c , s , e , ws , ps ⟫ , i) ⇒ D)
case∷-preserves-⇒ (Deposit x x₁ x₂ x₃) = Deposit (∷-preserves-∈ x) x₁ x₂ x₃
case∷-preserves-⇒ (Choice x x₁ x₂ x₃) = Choice (∷-preserves-∈ x) x₁ x₂ x₃
case∷-preserves-⇒ (Notify x x₁ x₂ x₃) = Notify (∷-preserves-∈ x) x₁ x₂ x₃

⇒-eval :
  ∀ (C : Configuration)
  → (i : TransactionInput)
  → ℕ
  → (Σ[ D ∈ Configuration ] (((C , i) ⇒ D) × (Quiescent D))) ⊎ TransactionError
⇒-eval
  ⟪ When [] (mkTimeout (mkPosixTime t)) c
  , s
  , e
  , w
  , p
  ⟫
  (mkTransactionInput (mkInterval (mkPosixTime tₛ) Δₜ) _)
  _ = inj₂ TEApplyNoMatchError
⇒-eval
  ⟪ When cs (mkTimeout (mkPosixTime t)) c
  , s
  , e
  , w
  , p
  ⟫
  (mkTransactionInput (mkInterval (mkPosixTime tₛ) Δₜ) [])
  _ = inj₂ TEUselessTransaction
⇒-eval
  ⟪ When (mkCase (Deposit a₁ p₁ t₁ v) cₐ ∷ cs) (mkTimeout (mkPosixTime t)) c
  , s
  , e
  , ws
  , ps
  ⟫
  (mkTransactionInput i (NormalInput (IDeposit a₂ p₂ t₂ n) ∷ is))
  (suc m)
  with a₁ ≟-AccountId a₂
     | p₁ ≟-Party p₂
     | t₁ ≟-Token t₂
     | ∣ ℰ⟦ v ⟧ e s ∣ ≟ n
     | interval-end e <? t
     | eval
       ⟪ cₐ
       , record s
         { accounts =
           ((a₁ , t₁) , n) ↑-update (accounts s)
         }
       , e
       , ws
       , ps
       ⟫
       m
... | yes refl
    | yes refl
    | yes refl
    | yes refl
    | yes tₑ<tₒ
    | (D , C⇀⋆D , inj₁ q)
    = inj₁ (D , Deposit (here refl) refl tₑ<tₒ (Reduce-until-quiescent C⇀⋆D q) , q)
... | _
    | _
    | _
    | _
    | _
    | _
    with ⇒-eval
       ⟪ When cs (mkTimeout (mkPosixTime t)) c
       , s
       , e
       , ws
       , ps
       ⟫
       (mkTransactionInput i (NormalInput (IDeposit a₂ p₂ t₂ n) ∷ is))
       m
... | inj₁ (D , C×i⇒D , q) = inj₁ (D , (case∷-preserves-⇒ C×i⇒D , q))
... | inj₂ err = inj₂ err
⇒-eval
  ⟪ When (mkCase (Choice i₁ b₁) cₐ ∷ cs) (mkTimeout (mkPosixTime t)) c
  , s
  , e
  , ws
  , ps
  ⟫
  (mkTransactionInput i (NormalInput (IChoice i₂ n₂) ∷ is))
  (suc m)
  with i₁ ≟-ChoiceId i₂
     | n₂ inBounds b₁ 𝔹.≟ true
     | interval-end e <? t
     | eval
       ⟪ cₐ
       , record s
         { choices =
           (i₁ , unChosenNum n₂) ↑-ChoiceId (choices s)
         }
       , e
       , ws
       , ps
       ⟫
       m
... | yes refl
    | yes p
    | yes tₑ<tₒ
    | (D , C⇀⋆D , inj₁ q)
    = inj₁ (D , Choice (here refl) p tₑ<tₒ (Reduce-until-quiescent C⇀⋆D q) , q)
... | _
    | _
    | _
    | _
    with ⇒-eval
       ⟪ When cs (mkTimeout (mkPosixTime t)) c
       , s
       , e
       , ws
       , ps
       ⟫
       (mkTransactionInput i (NormalInput (IChoice i₂ n₂) ∷ is))
       m
... | inj₁ (D , C×i⇒D , q) = inj₁ (D , (case∷-preserves-⇒ C×i⇒D , q))
... | inj₂ err = inj₂ err
⇒-eval
  ⟪ When (mkCase (Notify o) cₐ ∷ cs) (mkTimeout (mkPosixTime t)) c
  , s
  , e
  , ws
  , ps
  ⟫
  (mkTransactionInput i (NormalInput INotify ∷ is))
  (suc m)
  with 𝒪⟦ o ⟧ e s 𝔹.≟ true
     | interval-end e <? t
     | eval
       ⟪ cₐ
       , s
       , e
       , ws
       , ps
       ⟫
       m
... | yes o≡true
    | yes tₑ<tₒ
    | (D , C⇀⋆D , inj₁ q)
    = inj₁ (D , Notify (here refl) o≡true tₑ<tₒ (Reduce-until-quiescent C⇀⋆D q) , q)
... | _
    | _
    | _
    with ⇒-eval
       ⟪ When cs (mkTimeout (mkPosixTime t)) c
       , s
       , e
       , ws
       , ps
       ⟫
       (mkTransactionInput i (NormalInput INotify ∷ is))
       m
... | inj₁ (D , C×i⇒D , q) = inj₁ (D , (case∷-preserves-⇒ C×i⇒D , q))
... | inj₂ err = inj₂ err
⇒-eval C x _ = inj₂ TEUselessTransaction


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
    → C ↠ D
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
    ∀ {i C D ws ps s}
    → warnings C ≡ []
    → payments C ≡ []
    → (C , i) ⇒ D
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

  done :
    ∀ {s}
    → accounts s ≡ []
    -----------------
    → (Close , s) ⇓
      ⟦ []
      , []
      , s
      ⟧


⇓-eval :
  ∀ (c : Contract)
  → (s : State)
  → (is : List TransactionInput)
  → ℕ
  → (Σ[ r ∈ Result ] (c , s) ⇓ r) ⊎ TransactionError
⇓-eval _ _ _ zero = inj₂ TEUselessTransaction
⇓-eval Close s@(⟨ [] , _ , _ , _ ⟩) [] _ = inj₁ (⟦ [] , [] , s ⟧ , done refl)
⇓-eval c@(When _ _ _) s (i ∷ is) (suc m)
  with ⇒-eval
       ⟪ c
       , s
       , mkEnvironment (mkInterval (mkPosixTime 0) 0)
       , []
       , []
       ⟫
       i
       m
... | inj₂ _ = inj₂ TEUselessTransaction
... | inj₁ (D , C×i⇒D , _) with ⇓-eval (contract D) (state D) is m
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) =
      inj₁ (⟦ ws ++ convertReduceWarnings (warnings D)
            , ps ++ payments D
            , s
            ⟧
            , apply-inputs refl refl C×i⇒D d×s×is⇓r
           )
... | inj₂ err = inj₂ err
⇓-eval c s is (suc m)
  with eval
       ⟪ c
       , s
       , mkEnvironment (mkInterval (mkPosixTime 0) 0)
       , []
       , []
       ⟫
       m
... | _ , _ , inj₂ _ = inj₂ TEUselessTransaction
... | D , C×i⇒D , inj₁ q with ⇓-eval (contract D) (state D) is m
... | inj₁ (⟦ ws , ps , s ⟧ , d×s×is⇓r) =
      inj₁ (⟦ ws ++ convertReduceWarnings (warnings D)
            , ps ++ payments D
            , s
            ⟧
            , reduce-until-quiescent refl refl (Reduce-until-quiescent C×i⇒D q) d×s×is⇓r
           )
... | inj₂ err = inj₂ err

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
      (Reduce-until-quiescent
        ((⟪ c , s , e , [] , [] ⟫) ⇀⟨ AssertFalse refl ⟩ (⟪ d , s , e , [ ReduceAssertionFailed ] , [] ⟫) ∎)
        (waiting (s≤s (s≤s (s≤s z≤n)))))
      (apply-inputs {i = i} refl refl (Deposit (here refl) refl (s≤s (s≤s (s≤s z≤n)))
        (Reduce-until-quiescent
          (⟪ Close , ⟨ [((a₁ , t) , 1)] , [] , [] , minTime s ⟩ , e , []  , [] ⟫
                 ⇀⟨ CloseRefund ⟩ (⟪ Close , ⟨ [] , [] , [] , (minTime s) ⟩ , e , [] , [ a₁ [ t , 1 ]↦ mkParty p₁ ] ⟫) ∎)
          close))
        (done refl))

  _ = ⇓-eval c s (i ∷ []) 100 ≡
       inj₁ (
         ⟦ [ TransactionAssertionFailed ]
         , [ a₁ [ t , 1 ]↦ mkParty p₁ ]
         , s
         ⟧ , reduction-steps)
