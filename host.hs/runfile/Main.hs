module Main where

-- import           Debug.Trace

import Control.Concurrent (forkFinally)
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
    [!edhFile] -> do
      !console <- defaultEdhConsole defaultEdhConsoleSettings
      let !consoleOut = consoleIO console . ConsoleOut
          runIt = do
            world <- createEdhWorld console
            installEdhBatteries world

            -- install batteries provided by nedh
            installNetBatteries world

            -- install batteries provided by hasdim
            installDimBatteries world

            runEdhFile world edhFile >>= \case
              Left !err -> do
                -- program crash on error
                consoleOut "HasDim crashed with an error:\n"
                consoleOut $ T.pack $ show err <> "\n"
              Right !phv -> case edhUltimate phv of
                -- clean program halt, all done
                EdhNil -> return ()
                -- unclean program exit
                _ -> do
                  consoleOut "HasDim halted with a result:\n"
                  consoleOut $
                    (<> "\n") $ case phv of
                      EdhString msg -> msg
                      _ -> T.pack $ show phv

      void $
        forkFinally runIt $ \ !result -> do
          case result of
            Left (e :: SomeException) ->
              consoleOut $ "💥 " <> T.pack (show e)
            Right _ -> pure ()
          -- shutdown console IO anyway
          consoleIO console ConsoleShutdown

      consoleIOLoop console
    _ -> hPutStrLn stderr "Usage: rundim <.edh-file>" >> exitFailure
