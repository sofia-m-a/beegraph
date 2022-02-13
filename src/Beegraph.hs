{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Beegraph
  ( Language,
    type Id,
    Beegraph,
    type BG,
    emptyBee,
    insertBee,
    unionBee,
    unionBeeId,
    type Weighted,
    astDepth,
    astSize,
    extractBee,
    queryByShape,
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)), coiter, _extract, _unwrap)
import Control.Lens hiding ((:<))
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Foldable (maximum)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Sequence (Seq ((:<|), (:|>)))
import Data.Traversable (for)
import Witherable (Witherable (wither), mapMaybe)
import Prelude hiding (mapMaybe)

class (Traversable f, Ord (f Id)) => Language f

newtype Id = Id {_unId :: Int}
  deriving (Eq, Ord, Show, Generic)

instance Hashable Id

makeLenses ''Id

data Node f = Node
  { -- union-find fields
    _ufParent :: !Id,
    _ufRank :: !Word16,
    _shape :: !(f Id)
  }

makeLenses ''Node

data Beegraph f i = Beegraph
  { -- map from id to node
    _nodes :: !(IntMap (Node f)),
    -- map from id to set of nodes in which it occurs
    _places :: !(IntMap IntSet),
    -- map from node shape to id
    _shapes :: !(Map (f Id) Id),
    -- the next 'Id' to use
    _next :: !Id
  }

makeLenses ''Beegraph

type BG f i a = State (Beegraph f i) a

emptyBee :: Language f => Beegraph f i
emptyBee = Beegraph mempty mempty mempty (Id 0)

-- union-find
ufInsert :: f Id -> BG f i Id
ufInsert node = do
  n <- use next
  next . unId += 1
  nodes . at (_unId n) .= Just (Node n 0 node)
  pure n

ufFind :: Id -> BG f i Id
ufFind i = do
  n <- preuse (nodes . ix (_unId i))
  if
      | Just (Node j' _ _) <- n,
        i /= j' -> do
        -- chase parent pointers, path compression
        grandparent <- preuse (nodes . ix (_unId j') . ufParent)
        for_ grandparent (\gp -> nodes . ix (_unId i) . ufParent .= gp)
        ufFind j'
      | otherwise -> do
        pure i

ufUnion :: Id -> Id -> BG f i (Maybe Id)
ufUnion a' b' = do
  a <- ufFind a'
  b <- ufFind b'
  an' <- preuse (nodes . ix (_unId a))
  bn' <- preuse (nodes . ix (_unId b))
  if
      | a /= b,
        Just an <- an',
        Just bn <- bn' -> do
        let (larger, smaller) = if an ^. ufRank > bn ^. ufRank then (a, b) else (b, a)
        nodes . ix (_unId smaller) . ufParent .= larger
        when (an ^. ufRank == bn ^. ufRank) $
          nodes . ix (_unId larger) . ufRank += 1
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
  s <- preuse (places . ix (_unId j'))
  let s' = (j',) <$> s
  whenNothing s' do
    places . at (_unId j') .= Just mempty
    --watcher %= ($ Insert (j', i)) . unwrap

    canonicalized <- traverse ufFind i

    -- construct union of occurrences, while also setting 'i' as an occurence for each subterm
    merges' <-
      fold <$> for i \v -> do
        p <- preuse (places . ix (_unId v))
        if
            | Just p' <- p -> do
              places . ix (_unId v) . at (_unId j') .= Just ()
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
  s <- preuse (nodes . ix (_unId i) . shape)
  if
      | Just s' <- s -> do
        f <- traverse ufFind s'
        fst <$> addTerm f
      | otherwise -> pure i

insertBee :: Language f => f Id -> BG f i Id
insertBee = fmap fst . addTerm

unionBeeId :: Language f => Id -> Id -> BG f i ()
unionBeeId a b = do
  c <- preuse (nodes . ix (_unId a) . shape)
  d <- preuse (nodes . ix (_unId b) . shape)
  fromMaybe (pure ()) $ unionBee <$> c <*> d

unionBee :: Language f => f Id -> f Id -> BG f i ()
unionBee a' b' = do
  (a, ai) <- addTerm a'
  (b, bi) <- addTerm b'
  u <- ufUnion a b
  whenJust u \u' -> do
    --watcher %= ($ Union (a, a') (b, b')) . unwrap
    -- u is the newly-unioned class, if we had to union them
    places . at (_unId a) .= Nothing
    places . at (_unId b) .= Nothing
    places . at (_unId u') .= Just (ai <> bi)
    la <-
      fromList <$> for (IntSet.toList ai) \i -> do
        i' <- canonicalize (Id i)
        pure (_unId i', Id i)
    lb <-
      fromList <$> for (IntSet.toList ai) \i -> do
        i' <- canonicalize (Id i)
        pure (_unId i', Id i)
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
        lift (ix (_unId index') . minTree .= Just tree)
        add (Any True)

    propagate :: AccumT Any (State (IntMap (Extractor f a))) ()
    propagate = do
      map' <- lift get
      ifor_ map' \index'' node ->
        let index' = Id index''
         in do
              let nep = node ^. exParent
              -- propagate from below
              newWeighted <- sequenceA <$> for (node ^. exSat) (\i -> lift (preuse (ix (_unId i) . minTree . _Just)))
              whenJust
                newWeighted
                ( \f -> do
                    let weighed = weigh (fmap extract f) :< f
                    update weighed node index'
                )
              -- propagate from above
              if
                  | index' /= nep,
                    Just p <- map' ^? (ix (_unId nep) . minTree . _Just) -> do
                    update p node index'
                  | otherwise -> pure ()
              -- propagate upwards
              if
                  | index' /= nep,
                    Just tree <- node ^. minTree,
                    Just p <- map' ^? ix (_unId nep) ->
                    update tree p nep
                  | otherwise -> pure ()

submapBetween :: Ord k => (k, k) -> Map k a -> Map k a
submapBetween (l, h) m = eq
  where
    (_less, greaterEq) = Map.split l m
    (eq, _greater) = Map.split h greaterEq

queryByShape :: Language f => f () -> BG f i (Map (f Id) Id)
queryByShape shape' =
  submapBetween (shape' $> Id minBound, shape' $> Id maxBound) <$> use shapes

data LeapVal
  = Some Id
  | End
  deriving (Eq, Ord, Show)

type Leaper = Cofree ((->) (Maybe LeapVal))

data RingView a = RingView
  { _mini :: a,
    _seq :: Seq a,
    _maxi :: a
  }
  deriving (Show, Functor, Foldable, Traversable)

makeLenses ''RingView

rotateRingL :: RingView a -> RingView a
rotateRingL (RingView l m r) = case m of
  Empty -> RingView r Empty l
  l' :<| m' -> RingView l' (m' :|> r) l

-- I swear these are exhaustive

triejoin :: [Leaper LeapVal] -> Leaper LeapVal
triejoin ls = case fromList $ sortOn extract ls of
  Empty -> coiter (const $ const End) End
  a :<| Empty -> a
  l :<| (m :|> r) -> go (RingView l m r)
  -- same here
  where
    go :: RingView (Leaper LeapVal) -> Leaper LeapVal
    go r =
      let lo = r ^. mini . _extract
          hi = r ^. maxi . _extract
       in if
              | End <- lo -> coiter (const $ const End) End
              | lo == hi ->
                lo :< \seek ->
                  let s = (r ^. mini . _unwrap) seek in go (rotateRingL $ r & mini .~ s)
              | otherwise ->
                let s = (r ^. mini . _unwrap) (Just hi) in go (rotateRingL $ r & mini .~ s)

data Foo a
  = F a a
  | G Int
  deriving (Eq, Ord, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Foo a)