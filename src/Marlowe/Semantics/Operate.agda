
module Marlowe.Semantics.Operate where


open import Data.Bool using (if_then_else_)
open import Data.Integer using (_<?_; _⊔_)
open import Marlowe.Language.State
open import Primitives
open import Relation.Nullary.Decidable using (⌊_⌋)


data IntervalResult : Set where
  IntervalTrimmed : Environment → State → IntervalResult
  InvalidIntervalError : TimeInterval → IntervalResult
  IntervalInPastError : PosixTime → TimeInterval → IntervalResult


fixInterval : TimeInterval → State → IntervalResult
fixInterval interval state =
  let
    low = unPosixTime (Pair.fst interval)
    high = unPosixTime (Pair.snd interval)
  in
    if ⌊ high <? low ⌋
      then InvalidIntervalError interval
      else
        let
          curMinTime = State.minTime state
          newLow = low ⊔ unPosixTime curMinTime
          curInterval = record interval {fst = mkPosixTime newLow}
          env = record {timeInterval = curInterval}
          newState = record state {minTime = mkPosixTime newLow}
        in
          if ⌊ high <? unPosixTime curMinTime ⌋
            then IntervalInPastError curMinTime interval
            else IntervalTrimmed env newState
