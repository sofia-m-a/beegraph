module Main where

import BeeEff
import Beegraph
import Control.Comonad.Cofree (coiter)
import Data.Functor.Classes (Show1 (liftShowsPrec), showsBinaryWith, showsUnaryWith)
import GHC.Show (ShowS, showString)
import Match

main :: IO ()
main = putStrLn "goo"

data Foo a
  = F a a
  | G a
  | H a
  | X
  | Y
  | Z
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

findZs :: Watcher Foo IntSet
findZs =
  coiter
    ( \is ev -> case ev of
        Insert (i, Z) -> one i <> is
        Insert _ -> is
        Union _ _ -> is
    )
    mempty

instance Hashable a => Hashable (Foo a)

instance Language Foo

instance Show1 Foo where
  liftShowsPrec :: (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Foo a -> ShowS
  liftShowsPrec sp _ p (F x y) = showsBinaryWith sp sp "F" p x y
  liftShowsPrec sp _ p (G a) = showsUnaryWith sp "G" p a
  liftShowsPrec sp _ p (H a) = showsUnaryWith sp "H" p a
  liftShowsPrec _ _ _ X = showString "X"
  liftShowsPrec _ _ _ Y = showString "Y"
  liftShowsPrec _ _ _ Z = showString "Z"

-- debug :: (Show (f ()), Show (f Id)) => State (Beegraph f i) ()
-- debug = gets show >>= traceM

test :: Text
test = show $
  evaluatingState
    (emptyBee findZs)
    $ do
      x <- insertBee X
      X `unionBee` Y
      G x `unionBee` H x
      gx <- insertBee $ G x
      F gx x `unionBee` F gx gx
      extractBee astSize
