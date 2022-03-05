{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

module Relation where

data Rel
  = Null
  | Nary (Map Int Rel)



-- import Control.Lens hiding (Empty)
-- import Data.Heap qualified as Heap
-- import Data.Sequence (Seq (..))
-- import GHC.Exts qualified as Ext
-- import Text.Show qualified

-- -- data RStep
-- --   = Step
-- --   | Leap Int

-- -- data Rel
-- --   = Null
-- --   | WithMin Int (RStep -> Rel)

-- -- makePrisms ''Rel

-- -- instance One Rel where
-- --   type OneItem Rel = Int
-- --   one i = WithMin i (const Null)

-- -- instance IsList Rel where
-- --   type Item Rel = Int

-- --   fromList [] = Null
-- --   fromList (i : is) = WithMin i \case
-- --     Step -> fromList is
-- --     Leap n -> fromList (dropWhile (< n) is)

-- --   toList Null = []
-- --   toList (WithMin i k) = i : Ext.toList (k Step)

-- -- instance Show Rel where
-- --   show rel = "fromList " ++ show (Ext.toList rel)

-- -- relMembers :: Fold Rel Int
-- -- relMembers = folding Ext.toList

-- -- conjoin :: [Rel] -> Rel
-- -- conjoin =
-- --   fmap (preview _WithMin) >>> sequence >>> maybe Null (sortOn fst >>> fromList >>> go)
-- --   where
-- --     go :: Seq (Int, RStep -> Rel) -> Rel
-- --     go Empty = Null
-- --     go (rel :<| Empty) = review _WithMin rel
-- --     go (l :<| (mid :|> r)) =
-- --       let kSpin s = case s of
-- --             Null -> Null
-- --             WithMin a k -> go (mid :|> r :|> (a, k))
-- --        in if fst l == fst r
-- --             then WithMin (fst l) (kSpin . snd l)
-- --             else kSpin $ snd l (Leap (fst r))

-- -- disjoin :: [Rel] -> Rel
-- -- disjoin =
-- --   fmap (preview _WithMin) >>> catMaybes >>> fmap (uncurry Heap.Entry) >>> Heap.fromList >>> go Nothing
-- --   where
-- --     go :: Maybe Int -> Heap.Heap (Heap.Entry Int (RStep -> Rel)) -> Rel
-- --     go m =
-- --       Heap.viewMin >>> \case
-- --         Nothing -> Null
-- --         Just (Heap.Entry i k, rest) ->
-- --           let f step = case k step of
-- --                 Null -> go (m `max` Just i) rest
-- --                 WithMin i' k' -> go (m `max` Just i) $ Heap.insert (Heap.Entry i' k') rest
-- --            in if Just i <= m
-- --                 then f Step
-- --                 else WithMin i f

-- -- data Nary
-- --   = Never
-- --   | Nary Rel (Int -> Nary)

-- -- makePrisms ''Nary

-- -- debugTree :: Nary -> String
-- -- debugTree = toString . unlines . fmap (\(i, t) -> toText (replicate i ' ') <> t) . go (-1)
-- --   where
-- --     go i Never = [(i, "Never")]
-- --     go i (Nary rel k) = concatMap (\j -> (i + 1, show j <> ":") : go (i + 2) (k j)) (Ext.toList rel)

-- -- depthy :: Nary -> String
-- -- depthy = show . go
-- --   where
-- --     go Never = 0
-- --     go (Nary rel k) = 1 + go (k 0)