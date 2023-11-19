module Marlowe.Semantics.Reduce where

open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Bool.Properties using (_≟_; ¬-not)
open import Data.Integer as ℤ using (0ℤ; _≤_; _>_; ∣_∣; _<?_; _≤?_)
open import Data.Integer.Properties as ℤ using ()
open import Data.List using (List; []; _∷_; _++_; foldr; reverse; [_]; null; sum; filter; map)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈-List_)
open import Data.List.Relation.Unary.Any using (Any; lookup; _─_; _∷=_; here; there)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ; zero; suc; s≤s; _⊓_; _∸_; _+_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (1+n≰n; ≤-trans; +-identityʳ; +-comm; +-assoc; ≤⇒≯; m≤m+n; ≰⇒>; ≮⇒≥)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂)
import Data.String as String
open import Function.Base using (case_of_; _∘_)

open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (Dec; yes; no; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Empty using (⊥; ⊥-elim)

open import Marlowe.Language.Contract
open import Marlowe.Language.Input
open import Marlowe.Language.State
open import Marlowe.Language.Transaction
open import Marlowe.Semantics.Evaluate

open import Contrib.Data.List.AssocList
open Decidable _≟-AccountId×Token_ renaming (_↑_ to _↑-AccountId×Token_; _∈?_ to _∈?-AccountId×Token_)
open Decidable _≟-ChoiceId_ renaming (_‼_default_ to _‼-ChoiceId_default_) using (_∈?_)
open Decidable _≟-ValueId_ renaming (_‼_ to _‼-ValueId_; _‼_default_ to _‼-ValueId_default_; _∈?_ to _∈-ValueId?_) hiding (_↑_)

open Environment using (timeInterval)
open State using (accounts; boundValues; choices)
open TimeInterval using (startTime)

data ReduceWarning : Set where
  ReduceNonPositivePay : AccountId → Payee → Token → Int → ReduceWarning
  ReducePartialPay : AccountId → Payee → Token → ℕ → ℕ → ReduceWarning
  ReduceShadowing : ValueId → Int → Int → ReduceWarning
  ReduceAssertionFailed : ReduceWarning

record Configuration : Set where
  field contract : Contract
        state : State
        environment : Environment
        warnings : List ReduceWarning
        payments : List Payment

open Configuration

data _⇀_ : Configuration → Configuration → Set where

  CloseRefund :
    ∀ { a : AccountId }
      { t : Token }
      { i : ℕ }
      { as : AssocList (AccountId × Token) ℕ }
      { cs : AssocList ChoiceId Int }
      { vs : AssocList ValueId Int }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { e : Environment }
      { m : PosixTime }
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
        warnings = ws ;
        payments = mkPayment a (mkAccount a) t i ∷ ps
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
    → ℰ⟦ v ⟧ e s ℤ.≤ 0ℤ
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
        warnings = ReduceNonPositivePay a y t (ℰ⟦ v ⟧ e s) ∷ ws ;
        payments = ps
      }

  PayNoAccount :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { a : AccountId }
      { y : Payee }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → ℰ⟦ v ⟧ e s > 0ℤ
    → (a , t) ∉ accounts s
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
        warnings = ReducePartialPay a y t 0 ∣ ℰ⟦ v ⟧ e s ∣ ∷ ws ; -- TODO: proper warning?
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
    → (p : (aₛ , t) ∈ accounts s)
    -----------------------------
    → let m = proj₂ (lookup p)
          n = ∣ ℰ⟦ v ⟧ e s ∣
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
        state = record s { accounts = ((aₜ , t) , (m ⊓ n)) ↑-update (p ∷= (proj₁ (lookup p) , m ∸ n)) } ;
        environment = e ;
        warnings = if (m <ᵇ n) then ReducePartialPay aₛ (mkAccount aₜ) t m n ∷ ws else ws ;
        payments = ps
      }

  PayExternal :
    ∀ { s : State }
      { e : Environment }
      { v : Value }
      { a : AccountId }
      { t : Token }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { p : Party }
    → ℰ⟦ v ⟧ e s > 0ℤ
    → (q : (a , t) ∈ accounts s)
    -----------------------------
    → let m = proj₂ (lookup q)
          n = ∣ ℰ⟦ v ⟧ e s ∣
      in
      record {
        contract = Pay a (mkParty p) t v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s { accounts = q ∷= (proj₁ (lookup q) , m ∸ n) } ;
        environment = e ;
        warnings = if (m <ᵇ n) then ReducePartialPay a (mkParty p) t m n ∷ ws else ws ;
        payments = mkPayment a (mkParty p) t (m ⊓ n) ∷ ps
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
        warnings = ws ;
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
        warnings = ws ;
        payments = ps
      }

  WhenTimeout :
    ∀ { s : State }
      { t tₛ Δₜ : ℕ }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
      { cs : List Case }
    → t ℕ.≤ tₛ
    -----------------------------
    → record {
        contract = When cs (mkTimeout (mkPosixTime t)) c ;
        state = s;
        environment = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = s ;
        environment = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) ;
        warnings = ws ;
        payments = ps
      }

  LetShadow :
    ∀ { s : State }
      { e : Environment }
      { c : Contract }
      { i : ValueId }
      { v : Value }
      { vᵢ : Int }
      { ws ws' : List ReduceWarning }
      { ps : List Payment }
    → (i , vᵢ) ∈-List boundValues s
    → ws' ≡  ReduceShadowing i vᵢ (ℰ⟦ v ⟧ e s) ∷ ws
    ----------------------------------------------------
    → record {
        contract = Let i v c ;
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
        warnings = ws' ;
        payments = ps
      }

  LetNoShadow :
    ∀ { s : State }
      { e : Environment }
      { c : Contract }
      { i : ValueId }
      { v : Value }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → i ∉ boundValues s
    -----------------------------
    → record {
        contract = Let i v c ;
        state = s ;
        environment = e ;
        warnings = ws ;
        payments = ps
      }
      ⇀
      record {
        contract = c ;
        state = record s { boundValues = (i , ℰ⟦ v ⟧ e s) ∷ boundValues s } ;
        environment = e ;
        warnings = ws ;
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
        warnings = ws ;
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
        warnings = ReduceAssertionFailed ∷ ws ;
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
    ∀ { t tₛ Δₜ : ℕ }
      { m : PosixTime }
      { cases : List Case }
      { as : AssocList (AccountId × Token) ℕ }
      { cs : AssocList ChoiceId Int }
      { vs : AssocList ValueId Int }
      { c : Contract }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → let tₑ = tₛ + Δₜ
       in tₑ ℕ.< t
    ------------------------------------------
    → Quiescent record {
          contract = When cases (mkTimeout (mkPosixTime t)) c ;
          state =
            record
              { accounts = as ;
                choices = cs ;
                boundValues = vs ;
                minTime = m
              } ;
          environment = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) ;
          warnings = ws ;
          payments = ps
        }

data AmbiguousTimeInterval : Configuration → Set where

  AmbiguousTimeIntervalError :
    ∀ {t tₛ Δₜ : ℕ}
      { cs : List Case }
      { c : Contract }
      { s : State }
      { ws : List ReduceWarning }
      { ps : List Payment }
    → tₛ ℕ.< t
    → (tₛ + Δₜ) ℕ.≥ t
    → AmbiguousTimeInterval record {
           contract = When cs (mkTimeout (mkPosixTime t)) c ;
           state = s ;
           environment = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ) ;
           warnings = ws ;
           payments = ps
        }

data Reducible (C : Configuration) : Set where

  step : ∀ {D}
    → C ⇀ D
      -----------
    → Reducible C

  quiescent :
      Quiescent C
      -----------
    → Reducible C

  ambiguousTimeInterval :
      AmbiguousTimeInterval C
      -----------------------
    → Reducible C


progress : ∀ (C : Configuration) → Reducible C
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
  } = quiescent close
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
  } with ℰ⟦ v ⟧ e s ≤? 0ℤ | (a , t) ∈?-AccountId×Token (accounts s)
... | yes q | _ = step (PayNonPositive q)
... | no ¬p | yes q = step (PayInternalTransfer (ℤ.≰⇒> ¬p) q)
... | no ¬p | no ¬q = step (PayNoAccount (ℤ.≰⇒> ¬p) (¬Any⇒All¬ (accounts s) ¬q))
progress record
  { contract = Pay a (mkParty p) t v c
  ; state = s
  ; environment = e
  ; warnings = ws
  ; payments = ps
  } with ℰ⟦ v ⟧ e s ≤? 0ℤ | (a , t) ∈?-AccountId×Token (accounts s)
... | yes q | _ = step (PayNonPositive q)
... | no ¬p | yes q = step (PayExternal (ℤ.≰⇒> ¬p) q)
... | no ¬p | no ¬q = step (PayNoAccount (ℤ.≰⇒> ¬p) (¬Any⇒All¬ (accounts s) ¬q))
progress record
  { contract = If o c₁ c₂
  ; state = s
  ; environment = e
  ; warnings = _
  ; payments = _
  } with 𝒪⟦ o ⟧ e s ≟ true
... | yes p = step (IfTrue p)
... | no ¬p = step (IfFalse (¬-not ¬p))
progress record
  { contract = When cs (mkTimeout (mkPosixTime t)) c
  ; state = record
    { accounts = _ ;
      choices = _ ;
      boundValues = _ ;
      minTime = _
    }
  ; environment = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
  ; warnings = _
  ; payments = _
  } with (tₛ + Δₜ) ℕ.<? t | t ℕ.≤? tₛ
... | yes p | _ = quiescent (waiting p)
... | _ | yes q = step (WhenTimeout q)
... | no ¬p | no ¬q = ambiguousTimeInterval (AmbiguousTimeIntervalError (≰⇒> ¬q) (≮⇒≥ ¬p))
progress record
  { contract = Let i v c
  ; state = s@(record
    { accounts = _ ;
      choices = _ ;
      boundValues = vs ;
      minTime = _
    })
  ; environment = e
  ; warnings = ws
  ; payments = ps
  } with i ∈-ValueId? vs
... | yes p =
  let vᵢ = proj₂ (lookup p)
  in step (LetShadow {s} {e} {c} {i} {v} {vᵢ} {ws} {ReduceShadowing i vᵢ (ℰ⟦ v ⟧ e s) ∷ ws} {ps} (lookup∈-L p) refl)
  where
    lookup∈-L : ∀ {A B : Set} {a : A} {abs : AssocList A B} → (p : a ∈ abs) → (a , proj₂ (lookup p)) ∈-List abs
    lookup∈-L (here refl) = here refl
    lookup∈-L (there p) = there (lookup∈-L p)
... | no ¬p = step (LetNoShadow (¬Any⇒All¬ vs ¬p))
progress record
  { contract = Assert o c
  ; state = s
  ; environment = e
  ; warnings = _
  ; payments = _
  } with 𝒪⟦ o ⟧ e s ≟ true
... | yes p = step (AssertTrue p)
... | no ¬p = step (AssertFalse (¬-not ¬p))

data FinishedEvaluation (C : Configuration) : Set where

  steps : ∀ {D}
    → C ⇀⋆ D
    → FinishedEvaluation C

  ambiguousTimeInterval :
    FinishedEvaluation C

  done :
    FinishedEvaluation C

-- Evaluator
eval : ∀ (C : Configuration) → ℕ → FinishedEvaluation C
eval C zero = steps (C ∎)
eval C (suc m) with progress C
... | quiescent _ = steps (C ∎)
... | ambiguousTimeInterval _ = ambiguousTimeInterval
... | step {D} C⇀D with eval D m
...      | steps D⇀⋆E = steps ( C ⇀⟨ C⇀D ⟩ D⇀⋆E )
...      | _ = done


-- Examples

role₁ role₂ : Party
role₁ = Role (mkByteString "foo")
role₂ = Role (mkByteString "bar")

accountId₁ accountId₂ : AccountId
accountId₁ = mkAccountId role₁
accountId₂ = mkAccountId role₂

token₁ : Token
token₁ = mkToken (mkByteString "") (mkByteString "")

config₀ : Configuration
config₀ = record
  { contract = If TrueObs Close Close
  ; state = record
    { accounts = [ (accountId₁ , token₁ ) , 5 ]
    ; choices = []
    ; boundValues = []
    ; minTime = mkPosixTime 0
    }
  ; environment = mkEnvironment (mkInterval (mkPosixTime 0) 5)
  ; warnings = []
  ; payments = []
  }

config₁ : Configuration
config₁ = record
  { contract = Close
  ; state = record
    { accounts = [ ( accountId₁ , token₁ ) , 5 ]
    ; choices = []
    ; boundValues = []
    ; minTime = mkPosixTime 0
    }
  ; environment = mkEnvironment (mkInterval (mkPosixTime 0) 5)
  ; warnings = []
  ; payments = []
  }

config₂ : Configuration
config₂ = record
  { contract = Close
  ; state = record
    { accounts = []
    ; choices = []
    ; boundValues = []
    ; minTime = mkPosixTime 0
    }
  ; environment = mkEnvironment (mkInterval (mkPosixTime 0) 5)
  ; warnings = []
  ; payments = [ mkPayment accountId₁ (mkAccount accountId₁) token₁ 5 ]
  }

_ = eval config₀ 100 ≡ steps (config₀ ⇀⟨ IfTrue refl ⟩ config₁ ⇀⟨ CloseRefund ⟩ config₂ ∎)
