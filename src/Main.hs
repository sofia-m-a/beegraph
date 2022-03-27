module Main where

-- todo: clean up BeeEff
-- todo: ergonomic rewriting specs
-- todo: associative-commutative
-- todo: make BG a transformer >> introduce other stop conditions

import BeeEff
import Beegraph
import Data.Functor.Classes
import GHC.Show (Show (showsPrec))
import Prettyprinter.Render.Terminal (putDoc)
import Relation
import System.Console.Haskeline

main :: IO ()
main = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop =
      getInputLine "bf> "
        >>= \case
          Nothing -> pure ()
          Just ":q" -> pure ()
          Just line -> do
            case uncurry prettyPyro <$> analyze line of
              Nothing -> outputStrLn "umatched brackets" >> loop
              Just doc -> lift (putDoc doc) >> outputStrLn "" >> loop
