{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Beegraph
  ( Language,
    type Id,
    Event (..),
    type Watcher,
    Beegraph,
    watcher,
    type BG,
    emptyBee,
    insertBee,
    unionBee,
    unionBeeId,
    type Weighted,
    astDepth,
    astSize,
    extractBee,
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)), ComonadCofree (unwrap))
import Control.Lens hiding ((:<))
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Foldable (maximum)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Traversable (for)
import Witherable (Witherable (wither), mapMaybe)
import Prelude hiding (mapMaybe)

class (Traversable f, Eq (f Id), Hashable (f Id)) => Language f

type Id = Int

data Node f = Node
  { -- union-find fields
    _ufParent :: !Id,
    _ufRank :: !Word16,
    _shape :: !(f Id)
  }

makeLenses ''Node

data Event f
  = Insert (Id, f Id)
  | Union (Id, f Id) (Id, f Id)

type Watcher f = Cofree ((->) (Event f))

data Beegraph f i = Beegraph
  { -- map from id to node
    _nodes :: !(IntMap (Node f)),
    -- map from id to set of nodes in which it occurs
    _places :: !(IntMap IntSet),
    -- map from node shape to id
    _shapes :: !(HashMap (f Id) Id),
    -- the next 'Id' to use
    _next :: !Id,
    -- accumulated info
    _watcher :: Watcher f i
  }

makeLenses ''Beegraph

type BG f i a = State (Beegraph f i) a

emptyBee :: Language f => Watcher f i -> Beegraph f i
emptyBee = Beegraph mempty mempty mempty 0

-- union-find
ufInsert :: f Id -> BG f i Id
ufInsert node = do
  n <- use next
  next += 1
  nodes . at n .= Just (Node n 0 node)
  pure n

ufFind :: Id -> BG f i Id
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

ufUnion :: Id -> Id -> BG f i (Maybe Id)
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
addTerm :: Language f => f Id -> BG f i (Id, IntSet)
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
    watcher %= ($ Insert (j', i)) . unwrap

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

canonicalize :: Language f => Id -> BG f i Id
canonicalize i = do
  s <- preuse (nodes . ix i . shape)
  if
      | Just s' <- s -> do
        f <- traverse ufFind s'
        fst <$> addTerm f
      | otherwise -> pure i

insertBee :: Language f => f Id -> BG f i Id
insertBee = fmap fst . addTerm

unionBeeId :: Language f => Id -> Id -> BG f i ()
unionBeeId a b = do
  c <- preuse (nodes . ix a . shape)
  d <- preuse (nodes . ix b . shape)
  fromMaybe (pure ()) $ unionBee <$> c <*> d

unionBee :: Language f => f Id -> f Id -> BG f i ()
unionBee a' b' = do
  (a, ai) <- addTerm a'
  (b, bi) <- addTerm b'
  u <- ufUnion a b
  whenJust u \u' -> do
    watcher %= ($ Union (a, a') (b, b')) . unwrap
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
    for_ m (uncurry unionBeeId)

-- Extraction
type Weighted f a = Cofree f a

astDepth :: Foldable f => f Natural -> Natural
astDepth f = maximum f + 1

astSize :: Foldable f => f Natural -> Natural
astSize f = sum f + 1

data Extractor f a = Extractor
  { _exSat :: f Id,
    _exParent :: Id,
    _minTree :: Maybe (Weighted f a)
  }

makeLenses ''Extractor

fixpoint :: Monad m => (a -> AccumT Any m a) -> a -> m a
fixpoint f x = do
  (out, changed) <- runAccumT (f x) (Any False)
  if getAny changed
    then fixpoint f out
    else pure out

extractBee :: forall f a i. (Language f, Ord a) => (f a -> a) -> BG f i (IntMap (Weighted f a))
extractBee weigh = do
  get >>= (nodes . traversed . shape . traversed $ canonicalize)
  graph <- get
  let graph' = fmap (\n -> Extractor (n ^. shape) (n ^. ufParent) Nothing) (graph ^. nodes)
  let f = executingState graph' (fixpoint (const propagate) ())
  pure (mapMaybe _minTree f)
  where
    update :: Cofree f a -> Extractor f a -> Id -> AccumT Any (State (IntMap (Extractor f a))) ()
    update tree node index' = when (((\tree' -> extract tree < extract tree') <$> node ^. minTree) /= Just False) $
      do
        lift (ix index' . minTree .= Just tree)
        add (Any True)

    propagate :: AccumT Any (State (IntMap (Extractor f a))) ()
    propagate = do
      map' <- lift get
      ifor_ map' \index' node -> do
        let nep = node ^. exParent
        -- propagate from below
        newWeighted <- sequenceA <$> for (node ^. exSat) (\i -> lift (preuse (ix i . minTree . _Just)))
        whenJust
          newWeighted
          ( \f -> do
              let weighed = weigh (fmap extract f) :< f
              update weighed node index'
          )
        -- propagate from above
        if
            | index' /= nep,
              Just p <- map' ^? (ix nep . minTree . _Just) -> do
              update p node index'
            | otherwise -> pure ()
        -- propagate upwards
        if
            | index' /= nep,
              Just tree <- node ^. minTree,
              Just p <- map' ^? ix nep ->
              update tree p nep
            | otherwise -> pure ()
