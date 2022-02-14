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
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)), coiter, _extract, _unwrap)
import Control.Comonad.Cofree qualified as Cofree
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

class (Traversable f, Ord (f Id), Hashable (f Id)) => Language f

newtype Id = Id {_unId :: Int}
  deriving (Eq, Ord, Show, Generic)

instance Hashable Id

makeLenses ''Id

data Node f = Node
  { -- union-find fields
    _ufParent :: !Id,
    _ufRank :: !Word16
  }

makeLenses ''Node

data Beeclass f = Beeclass
  { _shapes :: !(Set (f Id)),
    _parents :: !(Set (f Id, Id))
  }

makeLenses ''Beeclass

data Beegraph f = Beegraph
  { -- union find: equivalence relation over beeclass-IDs
    _nodes :: !(IntMap (Node f)),
    -- maps beeclass-IDS to beeclasses
    _classes :: !(IntMap (Beeclass f)),
    _share :: !(HashMap (f Id) Id)
  }

makeLenses ''Beegraph

type BG f a = State (Beegraph f) a

emptyBee :: Language f => Beegraph f
emptyBee = Beegraph mempty mempty mempty

-- union-find
ufInsert :: BG f Id
ufInsert = do
  n <- fst . maybe 0 (+ 1) . IntMap.lookupMax <$> use nodes
  nodes . at n .= Just (Node (Id n) 0)
  pure (Id n)

ufFind :: Id -> BG f Id
ufFind i = do
  n <- preuse (nodes . ix (_unId i))
  if
      | Just (Node j' _) <- n,
        i /= j' -> do
        -- chase parent pointers, path compression
        grandparent <- preuse (nodes . ix (_unId j') . ufParent)
        for_ grandparent (\gp -> nodes . ix (_unId i) . ufParent .= gp)
        ufFind j'
      | otherwise -> do
        pure i

ufUnion :: Id -> Id -> BG f (Maybe Id)
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
canonicalize :: Language f => f Id -> BG f (f Id)
canonicalize = traverse ufFind

insertBee :: Language f => f Id -> BG f Id
insertBee f = do
  g <- canonicalize f
  m <- use (share . at g)
  whenNothing m do
    i <- ufInsert
    for_ g \j -> classes . ix (_unId j) . parents . at (g, i) .= Just ()
    share . at g .= Just i
    pure i

-- addTerm :: Language f => f Id -> BG f (Id, IntSet)
-- addTerm i = do
--   j <- preuse (shapes . ix i)
--   j' <- whenNothing j do
--     f <- ufInsert i
--     shapes . at i .= Just f
--     pure f
--   s <- preuse (places . ix (_unId j'))
--   let s' = (j',) <$> s
--   whenNothing s' do
--     places . at (_unId j') .= Just mempty
--     --watcher %= ($ Insert (j', i)) . unwrap

--     canonicalized <- traverse ufFind i

--     -- construct union of occurrences, while also setting 'i' as an occurence for each subterm
--     merges' <-
--       fold <$> for i \v -> do
--         p <- preuse (places . ix (_unId v))
--         if
--             | Just p' <- p -> do
--               places . ix (_unId v) . at (_unId j') .= Just ()
--               pure p'
--             | otherwise -> pure mempty
--     merges <- flip wither (IntSet.toList merges') \place -> do
--       node <- preuse (nodes . ix place . shape)
--       place' <- traverse (traverse ufFind) node
--       pure $
--         if
--             | Just place'' <- place', place'' == canonicalized -> Just (place'', canonicalized)
--             | otherwise -> Nothing

--     for_ merges (uncurry unionBee)
--     pure (j', mempty)

-- insertBee :: Language f => f Id -> BG f Id
-- insertBee = fmap fst . addTerm

-- unionBeeId :: Language f => Id -> Id -> BG f ()
-- unionBeeId a b = do
--   c <- preuse (nodes . ix (_unId a) . shape)
--   d <- preuse (nodes . ix (_unId b) . shape)
--   fromMaybe (pure ()) $ unionBee <$> c <*> d

-- unionBee :: Language f => f Id -> f Id -> BG f ()
-- unionBee a' b' = do
--   (a, ai) <- addTerm a'
--   (b, bi) <- addTerm b'
--   u <- ufUnion a b
--   whenJust u \u' -> do
--     --watcher %= ($ Union (a, a') (b, b')) . unwrap
--     -- u is the newly-unioned class, if we had to union them
--     places . at (_unId a) .= Nothing
--     places . at (_unId b) .= Nothing
--     places . at (_unId u') .= Just (ai <> bi)
--     la <-
--       fromList <$> for (IntSet.toList ai) \i -> do
--         i' <- canonicalize (Id i)
--         pure (_unId i', Id i)
--     lb <-
--       fromList <$> for (IntSet.toList ai) \i -> do
--         i' <- canonicalize (Id i)
--         pure (_unId i', Id i)
--     let m = IntMap.intersectionWith (,) la lb
--     for_ m (uncurry unionBeeId)

-- Extraction
type Weighted f a = Cofree f a

astDepth :: Foldable f => f Natural -> Natural
astDepth f = maximum f + 1

astSize :: Foldable f => f Natural -> Natural
astSize f = sum f + 1

data Extractor f a = Extractor
  { _exSat :: f Id,
    _exParent :: Id,
    _minTree :: Maybe (Weighted f (a, Id))
  }

makeLenses ''Extractor

fixpoint :: Monad m => (a -> AccumT Any m a) -> a -> m a
fixpoint f x = do
  (out, changed) <- runAccumT (f x) (Any False)
  if getAny changed
    then fixpoint f out
    else pure out

extractBee :: forall f a i. (Language f, Ord a) => (f a -> a) -> BG f (IntMap (Weighted f (a, Id)))
extractBee weigh = do
  get >>= (nodes . traversed . shape . traversed $ canonicalize)
  graph <- get
  let graph' = fmap (\n -> Extractor (n ^. shape) (n ^. ufParent) Nothing) (graph ^. nodes)
  let f = executingState graph' (fixpoint (const propagate) ())
  pure (mapMaybe _minTree f)
  where
    update :: Cofree f (a, Id) -> Extractor f a -> Id -> AccumT Any (State (IntMap (Extractor f a))) ()
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
                    let weighed = (weigh (fmap (fst . extract) f), index') :< f
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

queryByShape :: Language f => f () -> BG f (Map (f Id) Id)
queryByShape shape' =
  submapBetween (shape' $> Id minBound, shape' $> Id maxBound) <$> use shapes

data Foo a
  = F a a
  | G Int
  deriving (Eq, Ord, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Foo a)

instance Language Foo

data LeaperF k a
  = LeaperEnd
  | LeaperNext a a (k -> a)
  deriving (Functor)

data Ended a = KeepUp a | ForgetIt
  deriving (Eq, Ord, Functor)

type Leaper k a = Cofree (LeaperF k) (Ended a)

data RingView a = RingView
  { _mini :: a,
    _seq :: Seq a,
    _maxi :: a
  }
  deriving (Show, Functor, Foldable, Traversable)

makeLenses ''RingView

-- I swear these are exhaustive
rotateRingL :: RingView a -> RingView a
rotateRingL (RingView l m r) = case m of
  Empty -> RingView r Empty l
  l' :<| m' -> RingView l' (m' :|> r) l

leapJoin :: forall k. Ord k => [Leaper k k] -> Leaper k k
leapJoin ls = case fromList $ sortOn extract ls of
  Empty -> ForgetIt :< LeaperEnd
  a :<| Empty -> a
  l :<| (m :|> r) -> go (RingView l m r)
  -- same here
  where
    go :: RingView (Leaper k k) -> Leaper k k
    go r =
      let lo = r ^. mini . _extract
          hi = r ^. maxi . _extract
          alt f = go $ rotateRingL $ r & mini .~ f
       in if
              | ForgetIt <- lo -> ForgetIt :< LeaperEnd
              | lo == hi -> lo :< fmap alt (r ^. mini . _unwrap)
              | otherwise -> case r ^. mini . _unwrap of
                LeaperEnd -> ForgetIt :< LeaperEnd
                LeaperNext _ _ leap -> case hi of
                  KeepUp k -> alt (leap k)
                  ForgetIt -> ForgetIt :< LeaperEnd
