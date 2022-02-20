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
          Just line -> do loop

-- case prettyPyro <$> analyze line of
--   Nothing -> outputStrLn "umatched brackets" >> loop
--   Just doc -> lift (putDoc doc) >> outputStrLn "" >> loop

data Foo a
  = F a a
  | G Int
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Foo a)

instance Language Foo

instance Show1 Foo where
  liftShowsPrec sp sl p (F a b) = showsBinaryWith sp sp "F" p a b
  liftShowsPrec sp sl p (G i) = showsUnaryWith showsPrec "G" p i

test :: String
test = show $
  evaluatingState emptyBee $ do
    g0 <- insertBee (G 0)
    g1 <- insertBee (G 1)
    g2 <- insertBee (G 2)
    g3 <- insertBee (G 3)
    unionBee g1 g2
    fg2 <- insertBee (F g1 g2)
    fg22 <- insertBee (F g2 g2)
    unionBee fg22 g3
    rebuild
    extractBee astSize