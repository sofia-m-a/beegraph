{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

module Relation where

import Control.Lens
import Data.Map qualified as Map
import Data.Sequence (Seq ((:<|), (:|>)))
import GHC.Exts (Item)
import GHC.Show qualified as S

data Rel
  = Null
  | Nary (Map Int Rel)

makePrisms ''Rel

instance One Rel where
  type OneItem Rel = Int
  one i = Nary (fromList [(i, Null)])

relFromList :: [Int] -> Rel
relFromList = Nary . fromList . map (,Null)

debugTree :: Rel -> String
debugTree = toString . unlines . fmap (\(i, t) -> toText (replicate i ' ') <> t) . go (-1)
  where
    go i Null = [(i, "Never")]
    go i (Nary m) = concatMap (\(j, r) -> (i + 1, show j <> ":") : go (i + 2) r) (Map.toList m)

instance Show Rel where
  show = debugTree