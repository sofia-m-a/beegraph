{-# LANGUAGE TemplateHaskell #-}

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
import Data.Deriving (deriveShow1)
import Control.Lens (use, uses)

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

data Foo a
  = Bar a a a
  | Baz a a
  | Qux a
  | Lit Int
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''Foo

instance Language Foo

test :: String
test = evaluatingState emptyBee do
  l0 <- insertBee $ Lit 0
  l1 <- insertBee $ Lit 1
  l2 <- insertBee $ Lit 3
  l3 <- insertBee $ Lit 4
  q0 <- insertBee $ Qux l0
  unionBee q0 l0
  unionBee l0 l1
  bz1 <- insertBee $ Baz l0 l1
  s <- uses classes (fmap debugclass)
  pure $ show s