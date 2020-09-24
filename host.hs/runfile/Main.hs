
module Main where

import           Prelude
-- import           Debug.Trace

import           System.Environment
import           System.IO
import           System.Exit

import           Control.Monad
import           Control.Exception
import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.EHI
import           Language.Edh.Net
import           Dim.EHI


main :: IO ()
main = getArgs >>= \case
  [!edhFile] -> do

    !console <- defaultEdhConsole defaultEdhConsoleSettings
    let !consoleOut = writeTBQueue (consoleIO console) . ConsoleOut
        runIt       = do

          world <- createEdhWorld console
          installEdhBatteries world

          -- install batteries provided by nedh
          installNetBatteries world

          -- install batteries provided by hasdim
          installDimBatteries world

          runEdhFile world edhFile >>= \case
            Left !err -> atomically $ do
              -- program crash on error
              consoleOut "HasDim crashed with an error:\n"
              consoleOut $ T.pack $ show err <> "\n"
            Right !phv -> case edhUltimate phv of
              -- clean program halt, all done
              EdhNil -> return ()
              -- unclean program exit
              _      -> atomically $ do
                consoleOut "HasDim halted with a result:\n"
                consoleOut $ (<> "\n") $ case phv of
                  EdhString msg -> msg
                  _             -> T.pack $ show phv

    void $ forkFinally runIt $ \ !result -> do
      case result of
        Left (e :: SomeException) ->
          atomically $ consoleOut $ "💥 " <> T.pack (show e)
        Right _ -> pure ()
      -- shutdown console IO anyway
      atomically $ writeTBQueue (consoleIO console) ConsoleShutdown

    consoleIOLoop console

  _ -> hPutStrLn stderr "Usage: rundim <.edh-file>" >> exitFailure
