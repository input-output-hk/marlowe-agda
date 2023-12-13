{-# LANGUAGE OverloadedStrings #-}

module Serialization where

import qualified Data.Aeson as JSON
import Data.Aeson.Types
import Data.Text (pack)

import MAlonzo.Code.Agda.Builtin.Sigma
import MAlonzo.Code.Marlowe.Language.Contract
import MAlonzo.Code.Marlowe.Language.Input
import MAlonzo.Code.Marlowe.Language.State
import MAlonzo.Code.Marlowe.Language.Transaction
import MAlonzo.Code.Marlowe.Semantics.Operate
import MAlonzo.Code.Marlowe.Examples.Escrow
import MAlonzo.RTE

instance ToJSON T_ByteString_6 where
  toJSON (C_mkByteString_8 string) = String string

instance ToJSON T_Party_46 where
  toJSON (C_Address_48 address) =
    object
      ["address" .= address]
  toJSON (C_Role_50 name) =
    object
      ["role_token" .= name]

instance ToJSON T_AccountId_108 where
  toJSON (C_mkAccountId_110 party) = toJSON party

instance ToJSON T_Payee_414 where
  toJSON (C_mkAccount_416 acc) = object ["account" .= acc]
  toJSON (C_mkParty_418 party) = object ["party" .= party]

instance ToJSON T_Token_238 where
  toJSON (C_mkToken_240 currSym tokName) =
    object
      [ "currency_symbol" .= toJSON currSym
      , "token_name" .= toJSON tokName
      ]

instance ToJSON T_ChoiceName_144 where
  toJSON (C_mkChoiceName_146 name) = toJSON name

instance ToJSON T_ChoiceId_176 where
  toJSON (C_mkChoiceId_186 name party) =
    object
      [ "choice_name" .= name
      , "choice_owner" .= party
      ]

instance ToJSON T_ValueId_300 where
  toJSON (C_mkValueId_306 name) = toJSON name

instance ToJSON T_Observation_352 where
  toJSON (C_AndObs_380 lhs rhs) =
    object
      [ "both" .= lhs
      , "and" .= rhs
      ]
  toJSON (C_OrObs_382 lhs rhs) =
    object
      [ "either" .= lhs
      , "or" .= rhs
      ]
  toJSON (C_NotObs_384 v) =
    object
      ["not" .= v]
  toJSON (C_ChoseSomething_386 choiceId) =
    object
      ["chose_something_for" .= choiceId]
  toJSON (C_ValueGE_388 lhs rhs) =
    object
      [ "value" .= lhs
      , "ge_than" .= rhs
      ]
  toJSON (C_ValueGT_390 lhs rhs) =
    object
      [ "value" .= lhs
      , "gt" .= rhs
      ]
  toJSON (C_ValueLT_392 lhs rhs) =
    object
      [ "value" .= lhs
      , "lt" .= rhs
      ]
  toJSON (C_ValueLE_394 lhs rhs) =
    object
      [ "value" .= lhs
      , "le_than" .= rhs
      ]
  toJSON (C_ValueEQ_396 lhs rhs) =
    object
      [ "value" .= lhs
      , "equal_to" .= rhs
      ]
  toJSON C_TrueObs_398 = toJSON True
  toJSON C_FalseObs_400 = toJSON False

instance ToJSON T_Value_354 where
  toJSON (C_AvailableMoney_356 accountId token) =
    object
      [ "amount_of_token" .= token
      , "in_account" .= accountId
      ]
  toJSON (C_Constant_358 x) = toJSON x
  toJSON (C_NegValue_360 x) =
    object
      ["negate" .= x]
  toJSON (C_AddValue_362 lhs rhs) =
    object
      [ "add" .= lhs
      , "and" .= rhs
      ]
  toJSON (C_SubValue_364 lhs rhs) =
    object
      [ "value" .= lhs
      , "minus" .= rhs
      ]
  toJSON (C_MulValue_366 lhs rhs) =
    object
      [ "multiply" .= lhs
      , "times" .= rhs
      ]
  toJSON (C_DivValue_368 lhs rhs) =
    object
      [ "divide" .= lhs
      , "by" .= rhs
      ]
  toJSON (C_ChoiceValue_370 choiceId) =
    object
      ["value_of_choice" .= choiceId]
  toJSON C_TimeIntervalStart_372 = JSON.String $ pack "time_interval_start"
  toJSON C_TimeIntervalEnd_374 = JSON.String $ pack "time_interval_end"
  toJSON (C_UseValue_376 valueId) =
    object
      ["use_value" .= valueId]
  toJSON (C_Cond_378 obs tv ev) =
    object
      [ "if" .= obs
      , "then" .= tv
      , "else" .= ev
      ]

instance ToJSON T_Bound_402 where
  toJSON (C_mkBound_404 from to) =
    object
      [ "from" .= from
      , "to" .= to
      ]

instance ToJSON T_Action_406 where
  toJSON (C_Deposit_408 accountId party token val) =
    object
      [ "into_account" .= accountId
      , "party" .= party
      , "of_token" .= token
      , "deposits" .= val
      ]
  toJSON (C_Choice_410 choiceId bounds) =
    object
      [ "for_choice" .= choiceId
      , "choose_between" .= toJSONList (map toJSON bounds)
      ]
  toJSON (C_Notify_412 obs) =
    object
      ["notify_if" .= obs]

instance ToJSON T_Case_422 where
  toJSON (C_mkCase_424 act cont) =
    object
      [ "case" .= act
      , "then" .= cont
      ]

instance ToJSON T_Contract_420 where
  toJSON C_Close_426 = JSON.String $ pack "close"
  toJSON (C_Pay_428 accountId payee token value contract) =
    object
      [ "from_account" .= accountId
      , "to" .= payee
      , "token" .= token
      , "pay" .= value
      , "then" .= contract
      ]
  toJSON (C_If_430 obs cont1 cont2) =
    object
      [ "if" .= obs
      , "then" .= cont1
      , "else" .= cont2
      ]
  toJSON (C_When_432 caseList (C_mkTimeout_142 (C_mkPosixTime_44 timeout)) cont) =
    object
      [ "when" .= toJSONList (map toJSON caseList)
      , "timeout" .= timeout
      , "timeout_continuation" .= cont
      ]
  toJSON (C_Let_434 valId value cont) =
    object
      [ "let" .= valId
      , "be" .= value
      , "then" .= cont
      ]
  toJSON (C_Assert_436 obs cont) =
    object
      [ "assert" .= obs
      , "then" .= cont
      ]

instance ToJSON T_TransactionWarning_38 where
  toJSON (C_TransactionNonPositiveDeposit_40 party accId tok amount) =
    object
      [ "party" .= party
      , "asked_to_deposit" .= amount
      , "of_token" .= tok
      , "in_account" .= accId
      ]
  toJSON (C_TransactionNonPositivePay_42 accId payee tok amount) =
    object
      [ "account" .= accId
      , "asked_to_pay" .= amount
      , "of_token" .= tok
      , "to_payee" .= payee
      ]
  toJSON (C_TransactionPartialPay_44 accId payee tok paid expected) =
    object
      [ "account" .= accId
      , "asked_to_pay" .= expected
      , "of_token" .= tok
      , "to_payee" .= payee
      , "but_only_paid" .= paid
      ]
  toJSON (C_TransactionShadowing_46 valId oldVal newVal) =
    object
      [ "value_id" .= valId
      , "had_value" .= oldVal
      , "is_now_assigned" .= newVal
      ]
  toJSON C_TransactionAssertionFailed_48 = JSON.String $ pack "assertion_failed"

instance ToJSON T_Payment_18 where
  toJSON (C__'91'_'44'_'93''8614'__36 accountId payee token amount) =
    object
      [ "payment_from" .= accountId
      , "to" .= payee
      , "token" .= token
      , "amount" .= amount
      ]

instance ToJSON T_InputContent_30 where
  toJSON (C_IDeposit_32 accId party tok amount) =
    object
      [ "input_from_party" .= party
      , "that_deposits" .= amount
      , "of_token" .= tok
      , "into_account" .= accId
      ]
  toJSON (C_IChoice_34 choiceId (C_mkChosenNum_8 chosenNum)) =
    object
      [ "input_that_chooses_num" .= chosenNum
      , "for_choice_id" .= choiceId
      ]
  toJSON C_INotify_36 = JSON.String $ pack "input_notify"

instance ToJSON T_Input_38 where
  toJSON (C_NormalInput_40 content) = toJSON content

instance ToJSON T_TransactionInput_64 where
  toJSON (C_mkTransactionInput_74 (C_mkInterval_52 (C_mkPosixTime_44 start) delta) txInps) =
    object
      [ "tx_interval" .= timeIntervalJSON
      , "tx_inputs" .= toJSONList (map toJSON txInps)
      ]
    where
      timeIntervalJSON =
        object
          [ "from" .= start
          , "to" .= (start + delta)
          ]

instance ToJSON T_State_18 where
  toJSON (C_'10216'_'44'_'44'_'44'_'10217'_36 accounts choices boundValues (C_mkPosixTime_44 minTime)) =
      object
        [ "accounts" .= toJSONList (map toJSONAccountId accounts)
        , "choices" .= toJSONList (map toJSONChoiceId choices)
        , "boundValues" .= toJSONList (map toJSONValueId boundValues)
        , "minTime" .= minTime
        ]
    where
      toJSONAccountId (C__'44'__32 a b) =
        let (C__'44'__32 c t) = coe a
            (accId :: T_AccountId_108) = coe c
            (tok :: T_Token_238) = coe t
            (i :: Int) = coe b
        in toJSON ((accId , tok), i)
      toJSONValueId (C__'44'__32 a b) =
        let (valId :: T_ValueId_300) = coe a
            (i :: Int) = coe b
        in toJSON (valId, i)
      toJSONChoiceId (C__'44'__32 a b) =
        let (cid :: T_ChoiceId_176) = coe a
            (i :: Int) = coe b
        in toJSON (cid, i)
