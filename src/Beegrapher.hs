{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
-- needed for some 'Show' instances...
{-# LANGUAGE UndecidableInstances #-}

module Beegrapher () where

import Control.Lens
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Traversable (for)
import Witherable (Witherable (wither))

class (Traversable f, Eq (f Id), Hashable (f Id)) => Language f

type Id = Int

data Node f = Node
  { -- union-find fields
    _ufParent :: !Id,
    _ufRank :: !Word16,
    _shape :: !(f Id)
  }

deriving instance (Show (f Id)) => Show (Node f)

makeLenses ''Node

data Beegraph f = Beegraph
  { -- map from id to node
    _nodes :: !(IntMap (Node f)),
    -- map from id to set of nodes in which it occurs
    _places :: !(IntMap IntSet),
    -- map from node shape to id
    _shapes :: !(HashMap (f Id) Id),
    -- the next 'Id' to use
    _next :: !Id
  }

makeLenses ''Beegraph

deriving instance (Show (f Id)) => Show (Beegraph f)

type BG f a = State (Beegraph f) a

emptyBee :: Language f => Beegraph f
emptyBee = Beegraph mempty mempty mempty 0

-- union-find
ufInsert :: f Id -> BG f Id
ufInsert node = do
  n <- use next
  next += 1
  nodes . at n .= Just (Node n 0 node)
  pure n

ufFind :: Id -> BG f Id
ufFind i = do
  n <- preuse (nodes . ix i)
  if
      | Just (Node j' _ _) <- n,
        i /= j' -> do
        -- chase parent pointers, path compression
        grandparent <- preuse (nodes . ix j' . ufParent)
        for_ grandparent (\gp -> nodes . ix i . ufParent .= gp)
        ufFind j'
      | otherwise -> do
        pure i

ufUnion :: Id -> Id -> BG f (Maybe Id)
ufUnion a' b' = do
  a <- ufFind a'
  b <- ufFind b'
  an' <- preuse (nodes . ix a)
  bn' <- preuse (nodes . ix b)
  if
      | a /= b,
        Just an <- an',
        Just bn <- bn' -> do
        let (larger, smaller) = if an ^. ufRank > bn ^. ufRank then (a, b) else (b, a)
        nodes . ix smaller . ufParent .= larger
        when (an ^. ufRank == bn ^. ufRank) $
          nodes . ix larger . ufRank += 1
        pure (Just larger)
      | otherwise -> pure Nothing

-- congruence closure
addTerm :: Language f => f Id -> BG f (Id, IntSet)
addTerm i = do
  j <- preuse (shapes . ix i)
  j' <- whenNothing j do
    f <- ufInsert i
    shapes . at i .= Just f
    pure f
  s <- preuse (places . ix j')
  let s' = (j',) <$> s
  whenNothing s' do
    places . at j' .= Just mempty

    canonicalized <- traverse ufFind i

    -- construct union of occurrences, while also setting 'i' as an occurence for each subterm
    merges' <-
      fold <$> for i \v -> do
        p <- preuse (places . ix v)
        if
            | Just p' <- p -> do
              places . ix v . at j' .= Just ()
              pure p'
            | otherwise -> pure mempty
    merges <- flip wither (IntSet.toList merges') \place -> do
      node <- preuse (nodes . ix place . shape)
      place' <- traverse (traverse ufFind) node
      pure $
        if
            | Just place'' <- place', place'' == canonicalized -> Just (place'', canonicalized)
            | otherwise -> Nothing

    for_ merges (uncurry unionBee)
    pure (j', mempty)

canonicalize :: Language f => Id -> BG f Id
canonicalize i = do
  s <- preuse (nodes . ix i . shape)
  if
      | Just s' <- s -> do
        f <- traverse ufFind s'
        fst <$> addTerm f
      | otherwise -> pure i

unionBee :: Language f => f Id -> f Id -> BG f ()
unionBee a' b' = do
  (a, ai) <- addTerm a'
  (b, bi) <- addTerm b'
  u <- ufUnion a b
  whenJust u \u' -> do
    -- u is the newly-unioned class, if we had to union them
    places . at a .= Nothing
    places . at b .= Nothing
    places . at u' .= Just (ai <> bi)
    la <-
      fromList <$> for (IntSet.toList ai) \i -> do
        i' <- canonicalize i
        pure (i', i)
    lb <-
      fromList <$> for (IntSet.toList ai) \i -> do
        i' <- canonicalize i
        pure (i', i)
    let m = IntMap.intersectionWith (,) la lb
    for_ m \(c, d) -> do
      c' <- preuse (nodes . ix c . shape)
      d' <- preuse (nodes . ix d . shape)
      fromMaybe (pure ()) $ unionBee <$> c' <*> d'
