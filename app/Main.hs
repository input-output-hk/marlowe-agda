{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Aeson.Encode.Pretty
import Data.Aeson.Types
import MAlonzo.Code.Agda.Builtin.Sigma
import MAlonzo.Code.Data.Sum.Base
import MAlonzo.Code.Marlowe.Examples.Escrow
import MAlonzo.Code.Marlowe.Language.Contract
import MAlonzo.Code.Marlowe.Language.State
import MAlonzo.Code.Marlowe.Language.Transaction
import MAlonzo.Code.Marlowe.Semantics.Operate
import MAlonzo.RTE
import Serialization

main :: IO ()
main =
  case playTrace contract state inputs execBudget of
    C_inj'8321'_38 l -> printResult minTime inputs contract (coe l)
    C_inj'8322'_42 r -> printError r

  where
    (C__'44'__32 m p) = d_escrowExample_50
    (C__'44'__32 c i) = coe p

    contract :: T_Contract_420 = coe c
    minTime :: T_PosixTime_38 = coe m
    inputs :: [ T_TransactionInput_64 ] = coe i
    state = d_emptyState_38 minTime

    execBudget = 100

    printResult (C_mkPosixTime_44 t) inputs contract (C__'44'__32 x _) =
      let (C_'10214'_'44'_'44'_'10215'_924 ws ps s) = coe x
       in print . encodePretty $
            object
              [ "minTime" .= t
              , "contract" .= contract
              , "inputs" .= inputs
              , "output"
                  .= object
                    [ "warnings" .= ws
                    , "payments" .= ps
                    , "state" .= s
                    ]
              ]
    printError r = putStr "error"

    playTrace = d_'8659''45'eval_964
