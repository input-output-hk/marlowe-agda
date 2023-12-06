module Marlowe.Semantics.Operate where

open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Integer using (_<?_; _≤?_; _≟_ ; _⊔_; _⊓_; _+_; _-_; +_; 0ℤ ; _≤_ ; _>_ ; _≥_ ; _<_; ∣_∣)
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecSetoid using () renaming (_∈?_ to _∈?-List_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ; suc; zero)
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
    ∀ {a p t v n c e s ws ps cases cont timeout D is}
    → (mkCase (Deposit a p t v) c) ∈ cases
    → ∣ ℰ⟦ v ⟧ e s ∣ ≡ n
    → interval-end e ℕ.< timeout
    → ( ⟪ c
        , record s { accounts = ((a , t) , n) ↑-update (accounts s) }
        , e
        , ws
        , ps
        ⟫
      ) ↠ D
    -------------------------------------------------------------------
    → ( ⟪ When cases (mkTimeout (mkPosixTime timeout)) cont
        , s
        , e
        , ws
        , ps
        ⟫
      , record is { inputs = NormalInput (IDeposit a p t n) ∷ inputs is }
      ) ⇒ D

  Choice :
    ∀ {c cont i n s is bs ws ps cases timeout e D}
    → (mkCase (Choice i bs) c) ∈ cases
    → n inBounds bs ≡ true
    → interval-end e ℕ.< timeout
    → ( ⟪ c
        , record s { choices = (i , unChosenNum n) ↑-ChoiceId (choices s) }
        , e
        , ws
        , ps
        ⟫
      ) ↠ D
    -----------------------------------------------------------------
    → ( ⟪ When cases (mkTimeout (mkPosixTime timeout)) cont
        , s
        , e
        , ws
        , ps
        ⟫
      , record is { inputs = NormalInput (IChoice i n) ∷ inputs is }
      ) ⇒ D

  Notify :
    ∀ {c cont is s o cases timeout e ws ps D}
    → (mkCase (Notify o) c) ∈ cases
    → 𝒪⟦ o ⟧ e s ≡ true
    → interval-end e ℕ.< timeout
    → ( ⟪ c
        , s
        , e
        , ws
        , ps
        ⟫
      ) ↠ D
    ---------------------------------------------------
    → ( ⟪ When cases (mkTimeout (mkPosixTime timeout)) cont
        , s
        , e
        , ws
        , ps
        ⟫
      , record is { inputs = NormalInput INotify ∷ inputs is }
      ) ⇒ D


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

private

  timeout : PosixTime
  timeout = mkPosixTime 100

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
  d = When ([ mkCase (Deposit a₁ p₂ t v) Close ]) (mkTimeout timeout) Close

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
        (waiting (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))))
      (apply-inputs {i = i} refl refl (Deposit (here refl) refl (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
        (Reduce-until-quiescent
          (⟪ Close , ⟨ [((a₁ , t) , 1)] , [] , [] , minTime s ⟩ , e , []  , [] ⟫
                 ⇀⟨ CloseRefund ⟩ (⟪ Close , ⟨ [] , [] , [] , (minTime s) ⟩ , e , [] , [ a₁ [ t , 1 ]↦ mkParty p₁ ] ⟫) ∎)
          close))
        (done refl))
{-
  _ = ⇓-eval c s (i ∷ i ∷ []) ≡
       inj₁ (
         ⟦ [ TransactionAssertionFailed ]
         , [ a₁ [ t , 1 ]↦ mkParty p₁ ]
         , s
         ⟧ , reduction-steps)
-}

fixInterval : TimeInterval → State → IntervalResult
fixInterval i s =
  let mkInterval (mkPosixTime tₛ) Δₜ = i
      mkPosixTime tₘ = minTime s
      tₑ = tₛ ℕ.+ Δₜ
      tₛ′ = tₛ ℕ.⊔ tₘ
  in if tₑ ℕ.<ᵇ tₘ
       then mkIntervalError (IntervalInPastError (mkPosixTime tₘ) i)
       else IntervalTrimmed
              record { timeInterval = record i { startTime = mkPosixTime tₛ′ } }
              record s { minTime = mkPosixTime tₛ′ }
