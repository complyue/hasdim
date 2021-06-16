module Main where

-- import           Debug.Trace

import Control.Concurrent (forkFinally)
import Control.Exception (SomeException)
import Control.Monad
import qualified Data.Text as T
import GHCi.Signals
import Language.Edh.EHI
import Repl (edhProgLoop)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main = do
  -- don't crash on double Ctrl^C or Ctrl^\, mimic what GHCi is doing
  installSignalHandlers
  -- run the specified module, assuming `repl` semantics
  getArgs >>= \case
    [] -> runModu "dim"
    [edhModu] -> runModu edhModu
    _ -> hPutStrLn stderr "Usage: hasdim [ <edh-module> ]" >> exitFailure
  where
    runModu :: FilePath -> IO ()
    runModu !moduSpec = do
      !console <- defaultEdhConsole defaultEdhConsoleSettings
      let !consoleOut = consoleIO console . ConsoleOut

      void $
        forkFinally (edhProgLoop moduSpec console) $ \ !result -> do
          case result of
            Left (e :: SomeException) ->
              consoleOut $ "💥 " <> T.pack (show e)
            Right _ -> pure ()
          -- shutdown console IO anyway
          consoleIO console ConsoleShutdown

      consoleOut ">> Dimensional Modeling in Haskell <<\n"
      consoleOut
        "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:\n"
      consoleOut "  https://github.com/e-wrks/hasdim/tree/master/Tour\n"

      consoleIOLoop console
