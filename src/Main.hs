module Main where

-- todo: clean up BeeEff
-- todo: separate rebuilding step
-- todo: extractBee doesn't show sharing
-- todo: pattern matching
-- todo: associative-commutative
-- todo: make Id a newtype

import BeeEff
import Beegraph
import Match
import Prettyprinter.Render.Terminal (putDoc)
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
            case prettyPyro <$> analyze line of
              Nothing -> outputStrLn "umatched brackets" >> loop
              Just doc -> lift (putDoc doc) >> outputStrLn "" >> loop
