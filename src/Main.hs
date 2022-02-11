module Main where

import BeeEff
import Beegraph
import Beegrapher
import Data.Functor.Classes (Show1 (liftShowsPrec), showsBinaryWith, showsUnaryWith)
import GHC.Show (ShowS, showString)

main :: IO ()
main = putStrLn "goo"

data Foo a
  = F a a
  | G
  | H a
  | X
  | Y
  | Z
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Foo a)

instance Language Foo

instance Show1 Foo where
  liftShowsPrec :: (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Foo a -> ShowS
  liftShowsPrec sp _ p (F x y) = showsBinaryWith sp sp "F" p x y
  liftShowsPrec sp _ p (H a) = showsUnaryWith sp "H" p a
  liftShowsPrec _ _ _ G = showString "G"
  liftShowsPrec _ _ _ X = showString "X"
  liftShowsPrec _ _ _ Y = showString "Y"
  liftShowsPrec _ _ _ Z = showString "Z"

debug :: (Show (f ()), Show (f Id)) => State (Beegraph f) ()
debug = gets show >>= traceM

test :: Text
test = show $
  evaluatingState
    (Beegraph mempty mempty 0)
    $ do
      x <- insertBee X
      y <- insertBee Y
      hx <- insertBee $ H x
      g <- insertBee G
      hx `unionBee` g
      hy <- insertBee $ H y
      x `unionBee` y
      debug
      extractBee astSize
