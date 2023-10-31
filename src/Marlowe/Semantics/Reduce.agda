
module Marlowe.Semantics.Reduce where


open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Bool.Properties as 𝔹 using ()
open import Data.Integer using (_<?_; _≤?_; _≟_ ; _⊔_; _⊓_; _-_; 0ℤ ; _≤_ ; _>_ ; _≥_ ; _<_)
open import Data.Integer.Properties as ℤ using ()
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties as ℕ using ()
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂)
import Data.String as String
open import Function.Base using (case_of_)
open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate
open import Marlowe.Semantics.Operate using (
  ReduceWarning;
  ReduceNoWarning;
  ReduceNonPositivePay;
  ReducePartialPay;
  ReduceShadowing;
  ReduceAssertionFailed;
  moneyInAccount;
  updateMoneyInAccount;
  addMoneyToAccount)
open import Primitives
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Empty using (⊥; ⊥-elim)

open import Primitives
open Decidable _eqAccountIdTokenDec_  renaming (_‼_default_ to _‼ᵃ_default_) hiding (_∈?_)
open Decidable _eqChoiceId_ renaming (_‼_default_ to _‼ᶜ_default_) using (_∈?_)
open Decidable _eqValueId_ renaming (_‼_ to _‼ᵛ_; _‼_default_ to _‼ᵛ_default_; _∈?_ to _∈ᵛ?_)

open Environment using (timeInterval)
open State using (accounts; boundValues; choices)

record Configuration : Set where
  field contract : Contract
        state : State
        environment : Environment
        warnings : List ReduceWarning
        payments : List Payment

data _⇀_ : Configuration → Configuration → Set where

  CloseRefund :
    ∀ { e : Environment }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { as : AssocList (AccountId × Token) Int }
      { cs : AssocList ChoiceId Int }
      { vs : AssocList ValueId Int }
      { m : PosixTime }
      { a : AccountId }
      { t : Token }
      { i : Int }
    --------------------------------------------
    → record {
        contract = Close ;
        state = record {
          accounts = ((a , t) , i) ∷ as ;
          choices = cs ;
          boundValues = vs ;
          minTime = m
          } ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = Close ;
        state = record {
          accounts = as ;
          choices = cs ;
          boundValues = vs ;
          minTime = m
          } ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps ++ [ mkPayment a (mkAccount a) t i ]
      }

  PayNonPositive :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { a : AccountId }
      { y : Payee }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → ℰ⟦ v ⟧ e s ≤ 0ℤ
    -----------------------------
    → record {
        contract = Pay a y t v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNonPositivePay a y t (ℰ⟦ v ⟧ e s) ] ;
        payments = ps
      }

  PayInternalTransfer :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { aₛ aₜ : AccountId }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → ℰ⟦ v ⟧ e s > 0ℤ
    -----------------------------
    → let value = ℰ⟦ v ⟧ e s
          sₛ = (aₛ , t) ‼ᵃ accounts s default 0ℤ
          sₜ = (aₜ , t) ‼ᵃ accounts s default 0ℤ
          paid = sₛ ⊓ value
      in
      record {
        contract = Pay aₛ (mkAccount aₜ) t v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s {
          accounts =
            let v = sₛ - paid
                as = addMoneyToAccount aₜ t paid (accounts s)
            in updateMoneyInAccount aₛ t v as
          } ;
        environment = e ;
        warnings = ws ++ [ if ⌊ paid <? value ⌋
            then ReducePartialPay aₛ (mkAccount aₜ) t paid value
            else ReduceNoWarning
          ];
        payments = ps
      }

  PayExternal :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { aₓ : AccountId }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { p : Party }
    → ℰ⟦ v ⟧ e s > 0ℤ
    -----------------------------
    → let value = ℰ⟦ v ⟧ e s
          available = moneyInAccount aₓ t (accounts s)
          paid = available ⊓ value
      in
      record {
        contract = Pay aₓ (mkParty p) t v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s {
            accounts = updateMoneyInAccount aₓ t (available - paid) (accounts s)
          } ;
        environment = e ;
        warnings = ws ++ [ if ⌊ paid <? value ⌋
            then ReducePartialPay aₓ (mkParty p) t paid value
            else ReduceNoWarning
          ] ;
        payments = ps ++ [ mkPayment aₓ (mkParty p) t paid ]
      }

  IfTrue :
    ∀ { s : State }
      { e : Environment }
      { o : Observation }
      { c₁ c₂ : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ o ⟧ e s ≡ true
    -----------------------------
    → record {
        contract = If o c₁ c₂ ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c₁ ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  IfFalse :
    ∀ { s : State }
      { e : Environment }
      { o : Observation }
      { c₁ c₂ : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ o ⟧ e s ≡ false
    -----------------------------
    → record {
        contract = If o c₁ c₂ ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c₂ ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  WhenTimeout :
    ∀ { s : State }
      { e : Environment }
      { o : Observation }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { t : ℕ }
      { cs : List Case }
    → let (mkPosixTime startTime) = proj₁ (timeInterval e) in startTime ℕ.≥ t
    → let (mkPosixTime endTime) = proj₂ (timeInterval e) in endTime ℕ.≥ t
    -----------------------------------------------------------------------
    → record {
        contract = When cs (mkTimeout (mkPosixTime t)) c ;
        state = s;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  LetShadow :
    ∀ { s : State }
      { e : Environment }
      { o : Observation }
      { c : Contract }
      { vₓ : ValueId }
      { v : Value }
      { i : Int }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → vₓ ‼ᵛ boundValues s ≡ just i
    ------------------------------
    → record {
        contract = Let vₓ v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceShadowing vₓ i (ℰ⟦ v ⟧ e s) ] ;
        payments = ps
      }

  LetNoShadow :
    ∀ { s : State }
      { e : Environment }
      { o : Observation }
      { c : Contract }
      { vₓ : ValueId }
      { v : Value }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → vₓ ‼ᵛ boundValues s ≡ nothing
    -------------------------------
    → record {
        contract = Let vₓ v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s { boundValues = (vₓ , ℰ⟦ v ⟧ e s) ↑ boundValues s } ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  AssertTrue :
    ∀ { s : State }
      { e : Environment }
      { o : Observation }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ o ⟧ e s ≡ true
    -----------------------------
    → record {
        contract = Assert o c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceNoWarning ] ;
        payments = ps
      }

  AssertFalse :
    ∀ { s : State }
      { e : Environment }
      { o : Observation }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → 𝒪⟦ o ⟧ e s ≡ false
    -----------------------------
    → record {
        contract = Assert o c ;
        state = s ;
        environment = e ;
        warnings = ws;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = e ;
        warnings = ws ++ [ ReduceAssertionFailed ] ;
        payments = ps
      }


-- reflexive and transitive closure

infix  2 _⇀⋆_
infix  1 begin_
infixr 2 _⇀⟨_⟩_
infix  3 _∎

data _⇀⋆_ : Configuration → Configuration → Set where
  _∎ : ∀ M
      ------
    → M ⇀⋆ M

  _⇀⟨_⟩_ : ∀ L {M N}
    → L ⇀ M
    → M ⇀⋆ N
      ------
    → L ⇀⋆ N

begin_ : ∀ {M N}
  → M ⇀⋆ N
    ------
  → M ⇀⋆ N
begin M⇀⋆N = M⇀⋆N


data Quiescent : Configuration → Set where

  close :
    ∀ { e : Environment }
      { cs : AssocList ChoiceId Int }
      { vs : AssocList ValueId Int }
      { ws : List ReduceWarning }
      { m : PosixTime }
      { ps : List Payment }
    ---------------------------------
    → Quiescent record {
          contract = Close ;
          state =
            record
              { accounts = [] ;
                choices = cs ;
                boundValues = vs ;
                minTime = m
              } ;
            environment = e ;
            warnings = ws ;
            payments = ps
        }

  waiting :
    ∀ { e : Environment }
      { cases : List Case }
      { as : AssocList (AccountId × Token) Int }
      { cs : AssocList ChoiceId Int }
      { vs : AssocList ValueId Int }
      { m : PosixTime }
      { t : ℕ }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → let (mkPosixTime startTime) = proj₁ (timeInterval e) in startTime ℕ.< t
    -----------------------------------------------------------------------
    → Quiescent record {
          contract = When cases (mkTimeout (mkPosixTime t)) c ;
          state =
            record
              { accounts = as ;
                choices = cs ;
                boundValues = vs ;
                minTime = m
              } ;
            environment = e ;
            warnings = ws ;
            payments = ps
        }

-- Quiescent configurations do not reduce
Quiescent¬⇀ :
  ∀ { C₁ C₂ : Configuration }
  → Quiescent C₁
  ---------------------------
  → ¬ (C₁ ⇀ C₂)
Quiescent¬⇀ close ()
Quiescent¬⇀ { record
  { contract = When _ (mkTimeout (mkPosixTime (ℕ.suc _))) _
  ; state = _
  ; environment = mkEnvironment (mkPosixTime (ℕ.suc n₁) , _)
  ; warnings = _
  ; payments = _
  }} (waiting (ℕ.s≤s x)) (WhenTimeout (ℕ.s≤s x₁) _) =
  let p = ℕ.1+n≰n {n₁}
      q = ℕ.≤-trans x x₁
  in p q

-- If a configuration reduces, it is not quiescent
⇀¬Quiescent :
  ∀ { C₁ C₂ : Configuration }
  → C₁ ⇀ C₂
  → ¬ Quiescent C₁
⇀¬Quiescent C₁⇀C₂ q = Quiescent¬⇀ q C₁⇀C₂

data Progress (C : Configuration) : Set where

  step : ∀ {D}
    → C ⇀ D
      ----------
    → Progress C

  done :
      Quiescent C
      -----------
    → Progress C


progress : ∀ (C : Configuration) → Progress C
progress record
  { contract = Close
  ; state = record
    { accounts = [] ;
      choices = _ ;
      boundValues = _ ;
      minTime = _
    }
  ; environment = _
  ; warnings = _
  ; payments = _
  } = done close
progress record
  { contract = Close
  ; state = record
    { accounts = a ∷ as ;
      choices = _ ;
      boundValues = _ ;
      minTime = _
    }
  ; environment = _
  ; warnings = _
  ; payments = _
  } = step CloseRefund

progress record
  { contract = Pay a (mkAccount p) t v c
  ; state = s
  ; environment = e
  ; warnings = _
  ; payments = _
  } with ℰ⟦ v ⟧ e s ≤? 0ℤ
... | yes q = let t = PayNonPositive q in step t
... | no q = {!!}
progress record
  { contract = Pay a (mkParty p) t v c
  ; state = s
  ; environment = e
  ; warnings = _
  ; payments = _
  } with ℰ⟦ v ⟧ e s ≤? 0ℤ
... | yes q = let t = PayNonPositive q in step t
... | no q = {!!}

progress record
  { contract = If o c₁ c₂
  ; state = s
  ; environment = e
  ; warnings = _
  ; payments = _
  } with 𝒪⟦ o ⟧ e s 𝔹.≟ true
... | yes p = let t = IfTrue p in step t
... | no p = let t = IfFalse (𝔹.¬-not p) in step t

progress record
  { contract = When cs (mkTimeout (mkPosixTime t)) c
  ; state = record
    { accounts = _ ;
      choices = _ ;
      boundValues = _ ;
      minTime = _
    }
  ; environment = _
  ; warnings = _
  ; payments = _
  } = {!!}

progress record
  { contract = Let i v c
  ; state = record
    { accounts = _ ;
      choices = _ ;
      boundValues = vs ;
      minTime = _
    }
  ; environment = _
  ; warnings = _
  ; payments = _
  } with i ‼ᵛ vs
... | just v = {!!}
... | nothing = {!!} -- step (LetNoShadow {!!})

progress record
  { contract = Assert o c
  ; state = s
  ; environment = e
  ; warnings = _
  ; payments = _
  } with 𝒪⟦ o ⟧ e s 𝔹.≟ true
... | yes p = let t = AssertTrue p in step t
... | no p = let t = AssertFalse (𝔹.¬-not p) in step t
