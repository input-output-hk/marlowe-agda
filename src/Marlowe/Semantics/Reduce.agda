module Marlowe.Semantics.Reduce where

open import Data.Bool using (Bool; if_then_else_; not; _∧_; _∨_; true; false)
open import Data.Bool.Properties using (_≟_; ¬-not)
open import Data.Integer as ℤ using (ℤ; 0ℤ; _≤_; _>_; ∣_∣; _<?_; _≤?_)
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
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)

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
  ReduceNonPositivePay : AccountId → Payee → Token → ℤ → ReduceWarning
  ReducePartialPay : AccountId → Payee → Token → ℕ → ℕ → ReduceWarning
  ReduceShadowing : ValueId → ℤ → ℤ → ReduceWarning
  ReduceAssertionFailed : ReduceWarning

record Configuration : Set where
  constructor ⟪_,_,_,_,_⟫
  field contract : Contract
        state : State
        environment : Environment
        warnings : List ReduceWarning
        payments : List Payment

open Configuration

data _⇀_ : Configuration → Configuration → Set where

  CloseRefund : ∀ {a t n s ws ps e}
    --------------------------------
    → ⟪ Close
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

  PayNonPositive : ∀ {s e v a p t c ws ps}
    → ℰ⟦ v ⟧ e s ℤ.≤ 0ℤ
    --------------------------------------
    → ⟪ Pay a p t v c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , s
      , e
      , ReduceNonPositivePay a p t (ℰ⟦ v ⟧ e s) ∷ ws
      , ps
      ⟫

  PayNoAccount : ∀ {s e v a p t c ws ps}
    → ℰ⟦ v ⟧ e s > 0ℤ
    → (a , t) ∉ accounts s
    ------------------------------------
    → ⟪ Pay a p t v c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , s
      , e
      , ReducePartialPay a p t 0 ∣ ℰ⟦ v ⟧ e s ∣ ∷ ws -- TODO: proper warning?
      , ps
      ⟫

  PayInternalTransfer : ∀ {s e v aₛ aₜ t c ws ps}
    → ℰ⟦ v ⟧ e s > 0ℤ
    → (aₛ×t∈as : (aₛ , t) ∈ accounts s)
    --------------------------------------------
    → let
        m = proj₂ (lookup aₛ×t∈as)
        n = ∣ ℰ⟦ v ⟧ e s ∣
      in
      ⟪ Pay aₛ (mkAccount aₜ) t v c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , record s
          { accounts =
            ((aₜ , t) , (m ⊓ n)) ↑-update (aₛ×t∈as ∷= ((aₛ , t) , m ∸ n))
          }
      , e
      , if (m <ᵇ n)
          then ReducePartialPay aₛ (mkAccount aₜ) t m n ∷ ws
          else ws
      , ps
      ⟫

  PayExternal : ∀ {s e v a t c ws ps p}
    → ℰ⟦ v ⟧ e s > 0ℤ
    → (a×t∈as : (a , t) ∈ accounts s)
    -----------------------------------
    → let
        m = proj₂ (lookup a×t∈as)
        n = ∣ ℰ⟦ v ⟧ e s ∣
      in
      ⟪ Pay a (mkParty p) t v c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , record s
          { accounts =
            a×t∈as ∷= ((a , t) , m ∸ n)
          }
      , e
      , if (m <ᵇ n)
          then ReducePartialPay a (mkParty p) t m n ∷ ws
          else ws
      , a [ t , m ⊓ n ]↦ mkParty p ∷ ps
      ⟫

  IfTrue : ∀ {s e o c₁ c₂ ws ps}
    → 𝒪⟦ o ⟧ e s ≡ true
    ----------------------------
    → ⟪ If o c₁ c₂
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c₁
      , s
      , e
      , ws
      , ps
      ⟫

  IfFalse : ∀ {s e o c₁ c₂ ws ps}
    → 𝒪⟦ o ⟧ e s ≡ false
    -----------------------------
    → ⟪ If o c₁ c₂
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c₂
      , s
      , e
      , ws
      , ps
      ⟫

  WhenTimeout : ∀ {s t tₛ Δₜ c ws ps cs}
    → t ℕ.≤ tₛ
    -----------------------------------
    → let
        e = mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
      in
      ⟪ When cs (mkTimeout (mkPosixTime t)) c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , s
      , e
      , ws
      , ps
      ⟫

  LetShadow : ∀ {s e c i v vᵢ ws ws' ps}
    → (i , vᵢ) ∈-List boundValues s
    → ws' ≡ ReduceShadowing i vᵢ (ℰ⟦ v ⟧ e s) ∷ ws
    ----------------------------------------------
    → ⟪ Let i v c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , s
      , e
      , ws'
      , ps
      ⟫

  LetNoShadow : ∀ {s e c i v ws ps}
    → i ∉ boundValues s
    --------------------
    → ⟪ Let i v c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , record s
          { boundValues =
            (i , ℰ⟦ v ⟧ e s) ∷ boundValues s
          }
      , e
      , ws
      , ps
      ⟫

  AssertTrue : ∀ {s e o c ws ps}
    → 𝒪⟦ o ⟧ e s ≡ true
    ----------------------------
    → ⟪ Assert o c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , s
      , e
      , ws
      , ps
      ⟫

  AssertFalse : ∀ {s e o c ws ps}
    → 𝒪⟦ o ⟧ e s ≡ false
    -----------------------------
    → ⟪ Assert o c
      , s
      , e
      , ws
      , ps
      ⟫ ⇀
      ⟪ c
      , s
      , e
      , ReduceAssertionFailed ∷ ws
      , ps
      ⟫


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

  close : ∀ {e cs vs ws m ps}
    -------------------------
    → Quiescent
        ⟪ Close
        , ⟨ [] , cs , vs , m ⟩
        , e
        , ws
        , ps
        ⟫

  waiting : ∀ {t tₛ Δₜ cs s c ws ps}
    → (tₛ + Δₜ) ℕ.< t
    -------------------------------
    → Quiescent
        ⟪ When cs (mkTimeout (mkPosixTime t)) c
        , s
        , mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
        , ws
        , ps
        ⟫

data AmbiguousTimeInterval : Configuration → Set where

  AmbiguousTimeIntervalError : ∀ {t tₛ Δₜ cs c s ws ps}
    → tₛ ℕ.< t
    → (tₛ + Δₜ) ℕ.≥ t
    --------------------------------------------------
    → AmbiguousTimeInterval
        ⟪ When cs (mkTimeout (mkPosixTime t)) c
        , s
        , mkEnvironment (mkInterval (mkPosixTime tₛ) Δₜ)
        , ws
        , ps
        ⟫

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
  ⟫ with ℰ⟦ v ⟧ e s ≤? 0ℤ | (a , t) ∈?-AccountId×Token as
... | yes v≤0 | _           = step (PayNonPositive v≤0)
... | no  v≰0 | yes a×t∈as = step (PayInternalTransfer (ℤ.≰⇒> v≰0) a×t∈as)
... | no  v≰0 | no ¬a×t∈as = step (PayNoAccount (ℤ.≰⇒> v≰0) (¬Any⇒All¬ as ¬a×t∈as))
progress
  ⟪ Pay a (mkParty p) t v _
  , s@(⟨ as , _ , _ , _ ⟩)
  , e
  , _
  , _
  ⟫ with ℰ⟦ v ⟧ e s ≤? 0ℤ | (a , t) ∈?-AccountId×Token as
... | yes v≤0 | _           = step (PayNonPositive v≤0)
... | no  v≰0 | yes a×t∈as = step (PayExternal (ℤ.≰⇒> v≰0) a×t∈as)
... | no  v≰0 | no ¬a×t∈as = step (PayNoAccount (ℤ.≰⇒> v≰0) (¬Any⇒All¬ as ¬a×t∈as))
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
  ⟫ with i ∈-ValueId? vs
... | yes i∈vs =
  let vᵢ = proj₂ (lookup i∈vs)
  in step (LetShadow {s} {e} {c} {i} {v} {vᵢ} {ws} {ReduceShadowing i vᵢ (ℰ⟦ v ⟧ e s) ∷ ws} {ps} (lookup∈-L i∈vs) refl)
  where
    lookup∈-L : ∀ {A B : Set} {a : A} {abs : AssocList A B}
      → (a∈abs : a ∈ abs)
      → (a , proj₂ (lookup a∈abs)) ∈-List abs
    lookup∈-L (here refl) = here refl
    lookup∈-L (there a∈abs) = there (lookup∈-L a∈abs)
... | no ¬a∈abs = step (LetNoShadow (¬Any⇒All¬ vs ¬a∈abs))
progress
  ⟪ Assert o c
  , s
  , e
  , _
  , _
  ⟫ with 𝒪⟦ o ⟧ e s ≟ true
... | yes o≡true = step (AssertTrue o≡true)
... | no ¬o≡true = step (AssertFalse (¬-not ¬o≡true))

data _⇀ₙ_ : Configuration → Configuration → Set where

  Reduce-until-quiescent : ∀ {C D}
    → C ⇀⋆ D
    → Quiescent D
    -------------
    → C ⇀ₙ D

  Ambiguous-time-interval : ∀ {C D}
    → C ⇀⋆ D
    → AmbiguousTimeInterval D
    -------------------------
    → C ⇀ₙ D

  Execution-budget-exceeded : ∀ {C D}
    → C ⇀⋆ D
    ---------
    → C ⇀ₙ D

-- Evaluator

eval :
  ∀ (C : Configuration)
  → ℕ
  → Σ[ D ∈ Configuration ] (C ⇀ₙ D)
eval C zero = C , Execution-budget-exceeded (C ∎)
eval C (suc m) with progress C
... | quiescent q = C , Reduce-until-quiescent (C ∎) q
... | ambiguousTimeInterval a = C , Ambiguous-time-interval (C ∎) a
... | step {D} C⇀D with eval D m
...      | E , Reduce-until-quiescent D⇀⋆E s = E , Reduce-until-quiescent (C ⇀⟨ C⇀D ⟩ D⇀⋆E) s
...      | E , Ambiguous-time-interval D⇀⋆E a = E , Ambiguous-time-interval (C ⇀⟨ C⇀D ⟩ D⇀⋆E) a
...      | E , Execution-budget-exceeded D⇀⋆E = E , Execution-budget-exceeded (C ⇀⟨ C⇀D ⟩ D⇀⋆E)

-- Examples

private
  role₁ role₂ : Party
  role₁ = Role (mkByteString "foo")
  role₂ = Role (mkByteString "bar")

  accountId₁ accountId₂ : AccountId
  accountId₁ = mkAccountId role₁
  accountId₂ = mkAccountId role₂

  token₁ : Token
  token₁ = mkToken (mkByteString "") (mkByteString "")

  config₂ : Configuration
  config₂ =
    ⟪ If TrueObs Close Close
    , ⟨ [ (accountId₁ , token₁ ) , 5 ] , [] , [] , mkPosixTime 0 ⟩
    , mkEnvironment (mkInterval (mkPosixTime 0) 5)
    , []
    , []
    ⟫

  config₁ : Configuration
  config₁ =
    ⟪ Close
    , ⟨ [ ( accountId₁ , token₁ ) , 5 ] , [] , [] , mkPosixTime 0 ⟩
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
    , [ accountId₁ [ token₁ , 5 ]↦ mkParty (unAccountId accountId₁) ]
    ⟫

  _ = eval config₂ 100 ≡ (config₀ , Reduce-until-quiescent (config₂ ⇀⟨ IfTrue refl ⟩ config₁ ⇀⟨ CloseRefund ⟩ config₀ ∎) close)
