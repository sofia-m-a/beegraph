{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

module Relation where

import Control.Lens hiding (Empty)
import Data.Sequence ( Seq((:<|), (:|>)), Seq(..) )
import GHC.Exts (Item)
import GHC.Show qualified as S
import Data.Heap qualified as Heap
import GHC.Exts qualified as Ext
import qualified Data.Set as Set
import qualified Data.Map as Map

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
  show rel = "fromList " ++ show (Ext.toList rel)

relMembers :: Fold Rel Int
relMembers = folding Ext.toList

conjoin :: [Rel] -> Rel
conjoin =
  fmap (preview _WithMin) >>> sequence >>> maybe Null (sortOn fst >>> fromList >>> go)
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

data Nary a
  = Nullary
  | Nary a Rel (Int -> Nary a)

makePrisms ''Nary

data SetNary a
  = SetNullary
  | SetNary a (Set Int) (Int -> SetNary a)

setInsert :: Ord a => a -> Int -> SetNary a -> SetNary a
setInsert v i SetNullary = SetNary v (one i) (const SetNullary)
setInsert v i k@(SetNary u set'' f) = case compare v u of
  LT -> SetNary v (one i) (const k)
  EQ -> SetNary v (one i <> set'') f
  GT -> SetNary u set'' (setInsert v i . f)

toNary :: SetNary a -> Nary a
toNary SetNullary = Nullary
toNary (SetNary v set'' f) = Nary v (fromList $ Set.toAscList set'') (toNary . f)

debugTree :: Show a => Nary a -> String
debugTree = toString . unlines . fmap (\(i, t) -> toText (replicate i ' ') <> t) . go (-1)
  where
    go i Nullary = [(i, "Nullary")]
    go i (Nary a m k) = concatMap (\j -> (i + 1, show a <> " " <> show j <> ":") : go (i + 2) (k j)) (Ext.toList m)