module Main where

-- import           Debug.Trace

import Dim.EHI (installDimBatteries)
import Event.Analytics.EHI
import Language.Edh.EHI
import Language.Edh.Net (installNetBatteries)
import Language.Edh.Repl
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [] -> replWithModule "dim"
    [edhModu] -> replWithModule edhModu
    _ -> hPutStrLn stderr "Usage: hasdim [ <edh-module> ]" >> exitFailure
  where
    replWithModule :: FilePath -> IO ()
    replWithModule = edhRepl defaultEdhConsoleSettings $
      \ !world -> do
        let !consoleOut = consoleIO (edh'world'console world) . ConsoleOut

        -- install all necessary batteries
        installEdhBatteries world
        installNetBatteries world
        installEasBatteries world
        installDimBatteries world

        consoleOut $
          ">> Dimensional Modeling in Haskell <<\n"
            <> "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:\n"
            <> "  https://github.com/e-wrks/tour\n"
