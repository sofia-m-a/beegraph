{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

module Relation where

import Control.Lens hiding (Empty)
import Data.Heap qualified as Heap
import Data.Sequence (Seq (..))
import GHC.Exts qualified as Ext
import Text.Show qualified

data RStep
  = Step
  | Leap Int

data Rel
  = Null
  | WithMin Int (RStep -> Rel)

makePrisms ''Rel

instance One Rel where
  type OneItem Rel = Int
  one i = WithMin i (const Null)

instance IsList Rel where
  type Item Rel = Int

  fromList [] = Null
  fromList (i : is) = WithMin i \case
    Step -> fromList is
    Leap n -> fromList (dropWhile (< n) is)

  toList Null = []
  toList (WithMin i k) = i : Ext.toList (k Step)

instance Show Rel where
  show rel = show (Ext.toList rel)

conjoin :: [Rel] -> Rel
conjoin =
  fmap (preview _WithMin) >>> sequence >>> maybe Null (fromList >>> go)
  where
    go :: Seq (Int, RStep -> Rel) -> Rel
    go Empty = Null
    go (rel :<| Empty) = review _WithMin rel
    go (l :<| (mid :|> r)) =
      let kSpin s = case s of
            Null -> Null
            WithMin a k -> go (mid :|> r :|> (a, k))
       in if fst l == fst r
            then WithMin (fst l) (kSpin . snd l)
            else kSpin $ snd l (Leap (fst r))

disjoin :: [Rel] -> Rel
disjoin =
  fmap (preview _WithMin) >>> catMaybes >>> fmap (uncurry Heap.Entry) >>> Heap.fromList >>> go Nothing
  where
    go :: Maybe Int -> Heap.Heap (Heap.Entry Int (RStep -> Rel)) -> Rel
    go m =
      Heap.viewMin >>> \case
        Nothing -> Null
        Just (Heap.Entry i k, rest) ->
          let f step = case k step of
                Null -> go (m `max` Just i) rest
                WithMin i' k' -> go (m `max` Just i) $ Heap.insert (Heap.Entry i' k') rest
           in if Just i <= m
                then f Step
                else WithMin i f