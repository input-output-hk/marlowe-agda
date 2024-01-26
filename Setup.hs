{-# LANGUAGE ImportQualifiedPost #-}

import Distribution.Simple qualified as D
import Distribution.Simple.Setup qualified as D
import Distribution.Types.HookedBuildInfo qualified as D
import System.Process qualified as Process


main :: IO ()
main =
  D.defaultMainWithHooks userHooks
  where
    userHooks :: D.UserHooks
    userHooks = D.simpleUserHooks { D.preConf = preConfHook }

    preConfHook :: D.Args -> D.ConfigFlags -> IO D.HookedBuildInfo
    preConfHook _ _ = do 
      print "********** Generating Adga Files in src/MAlonzo"
      Process.callCommand "find src -name \"*.lagda.md\" -exec agda --compile --ghc-dont-call-ghc --local-interfaces {} \\;"
      print "********** DONE Generating Adga Files in src./MAlonzo"
      return D.emptyHookedBuildInfo

