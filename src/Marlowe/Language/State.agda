module Marlowe.Language.State where


open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; _∧_)
open import Data.List using ([])
open import Data.Nat using (ℕ; _≤_; _+_)
open import Data.Product using (_×_; _,_)
open import Marlowe.Language.Contract using (AccountId; ChoiceId; Token; ValueId; _eqAccountId_; _eqChoiceId_; _eqToken_; _eqValueId_)
open import Primitives using (AssocList; PosixTime; mkPosixTime)
open PosixTime using (getPosixTime)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

Accounts : Set
Accounts = AssocList (AccountId × Token) Int

postulate
  _eqAccountIdTokenDec_ : ∀ (x y : AccountId × Token) → Dec (x ≡ y)

record State : Set where
  constructor mkState
  field
    accounts : AssocList (AccountId × Token) ℕ
    choices : AssocList ChoiceId Int
    boundValues : AssocList ValueId Int
    minTime : PosixTime

emptyState : PosixTime → State
emptyState = mkState [] [] []

record TimeInterval : Set where
  constructor mkInterval
  field
    startTime : PosixTime
    offset : ℕ

endTime : TimeInterval → PosixTime
endTime (mkInterval (mkPosixTime s) o) = mkPosixTime (s + o)

record Environment : Set where
  constructor mkEnvironment
  field
    timeInterval : TimeInterval

