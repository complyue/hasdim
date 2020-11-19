module Main where

-- import           Debug.Trace

import Control.Concurrent (forkFinally)
import Control.Concurrent.STM (atomically, writeTBQueue)
import Control.Exception (SomeException)
import Control.Monad
import qualified Data.Text as T
import Dim.EHI (installDimBatteries)
import Language.Edh.EHI
import Language.Edh.Net (installNetBatteries)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [moduSpec] -> do
      !console <- defaultEdhConsole defaultEdhConsoleSettings
      let !consoleOut = writeTBQueue (consoleIO console) . ConsoleOut
          !consoleShutdown = writeTBQueue (consoleIO console) ConsoleShutdown
          consoleErr msg =
            consoleLogger console 50 Nothing $ ArgsPack [EdhString msg] odEmpty
          runIt = do
            world <- createEdhWorld console
            installEdhBatteries world

            -- install batteries provided by nedh
            installNetBatteries world

            -- install batteries provided by hasdim
            installDimBatteries world

            runEdhModule world moduSpec edhModuleAsIs >>= \case
              Left !err -> atomically $ do
                -- program crash on error
                consoleErr $
                  T.pack $
                    "Edh crashed with an error:\n"
                      <> show err
                      <> "\n"
                consoleShutdown
              Right !phv -> case edhUltimate phv of
                -- clean program halt, all done
                EdhNil -> return ()
                -- unclean program exit
                _ -> atomically $ do
                  consoleErr $
                    (<> "\n") $
                      "Edh halted with a result:\n"
                        <> case phv of
                          EdhString msg -> msg
                          _ -> T.pack $ show phv
                  consoleShutdown

      void $
        forkFinally runIt $ \ !result -> do
          case result of
            Left (e :: SomeException) ->
              atomically $ consoleOut $ "💥 " <> T.pack (show e)
            Right _ -> pure ()
          -- shutdown console IO anyway
          atomically $ writeTBQueue (consoleIO console) ConsoleShutdown

      consoleIOLoop console
    _ -> hPutStrLn stderr "Usage: rundimm <edh-module>" >> exitFailure
