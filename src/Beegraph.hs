{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Beegraph
  ( Language,
    type Id,
    Beeclass,
    shapes,
    Beegraph,
    parent,
    nodes,
    classes,
    share,
    type BG,
    emptyBee,
    insertBee,
    findBee,
    unionBee,
    rebuild,
    type Weighted,
    astDepth,
    astSize,
    extractBee,
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens hiding ((:<), (<.>))
import Control.Monad.ST (ST, runST)
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Array.Base (newListArray)
import Data.Array.ST (STArray)
import Data.Foldable (maximum)
import Data.Functor.Apply
import Data.Functor.Classes (Show1 (liftShowsPrec), showsBinaryWith, showsUnaryWith)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map (dropWhileAntitone)
import Data.Map qualified as Map
import Data.STRef (STRef, modifySTRef, newSTRef, readSTRef, writeSTRef)
import GHC.Show (Show (showsPrec))
import Witherable (Filterable, Witherable, mapMaybe)
import Prelude hiding (mapMaybe)

-- Ord and Traversable instance must be compatible
class (Traversable f, Ord (f Id)) => Language f

-- ────────────────────────────────── Id ─────────────────────────────────── --
newtype Id = Id {_unId :: Int}
  deriving (Eq, Ord, Generic)

instance Show Id where
  showsPrec p (Id y) = showsUnaryWith showsPrec "Id" p y

instance Bounded Id where
  minBound = Id 0
  maxBound = Id maxBound

instance Hashable Id

makeLenses ''Id

-- ───────────────────────────────── Node ────────────────────────────────── --
data Node f = Node
  { -- union-find fields
    _ufParent :: !Id,
    _ufRank :: !Word16
  }

makeLenses ''Node

-- ─────────────────────────────── Beeclass ──────────────────────────────── --
data Beeclass f = Beeclass
  { _shapes :: !(Set (f Id)),
    _parents :: !(Map (f Id) Id)
  }

makeLenses ''Beeclass

-- ─────────────────────────────── Beegraph ──────────────────────────────── --
data Beegraph f = Beegraph
  { -- union find: equivalence relation over beeclass-IDs
    _nodes :: !(IntMap (Node f)),
    -- maps beeclass-IDs to beeclasses
    _classes :: !(IntMap (Beeclass f)),
    -- maps shapes to IDs
    _share :: !(Map (f Id) Id),
    -- list of newly-unioned classes to process
    _worklist :: !IntSet
  }

makeLenses ''Beegraph

type BG f a = State (Beegraph f) a

emptyBee :: Language f => Beegraph f
emptyBee = Beegraph mempty mempty mempty mempty

parent :: Id -> Traversal' (Beegraph f) Id
parent i = nodes . ix (_unId i) . ufParent

-- ────────────────────────────── Union-find ─────────────────────────────── --
ufInsert :: BG f Id
ufInsert = do
  n <- maybe 0 ((+ 1) . fst) . IntMap.lookupMax <$> use nodes
  nodes . at n .= Just (Node (Id n) 0)
  pure (Id n)

ufFind :: Id -> BG f Id
ufFind i = do
  n <- preuse (nodes . ix (_unId i))
  if
      | Just (Node j' _) <- n,
        i /= j' -> do
        -- chase parent pointers and compress the path
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
        -- Union by rank
        let (larger, smaller) = if an ^. ufRank > bn ^. ufRank then (a, b) else (b, a)
        nodes . ix (_unId smaller) . ufParent .= larger
        when (an ^. ufRank == bn ^. ufRank) $
          nodes . ix (_unId larger) . ufRank += 1
        pure (Just larger)
      | otherwise -> pure Nothing

-- ────────────────────────── Congruence closure ─────────────────────────── --
canonicalize :: Language f => f Id -> BG f (f Id)
canonicalize = traverse ufFind

insertBee :: Language f => f Id -> BG f Id
insertBee f = do
  g <- canonicalize f
  m <- use (share . at g)
  whenNothing m do
    i <- ufInsert
    for_ g \j -> classes . ix (_unId j) . parents . at g .= Just i
    classes . at (_unId i) .= Just (Beeclass (one g) mempty)
    share . at g .= Just i
    pure i

findBee :: Language f => Id -> BG f Id
findBee = ufFind

unionBee :: Language f => Id -> Id -> BG f Id
unionBee a b = do
  u <- ufUnion a b
  if
      | Just u' <- u -> do
        worklist . at (_unId u') .= Just ()
        pure u'
      | Nothing <- u -> pure a

rebuild :: Language f => BG f ()
rebuild = do
  w <- use worklist
  when (IntSet.size w /= 0) do
    worklist .= mempty
    todo :: IntSet <- fmap (fromList . fmap _unId) . traverse (findBee . Id) . IntSet.toList $ w
    for_ (IntSet.toList todo) (repair . Id)
    rebuild

repair :: Language f => Id -> BG f ()
repair i = do
  p <- use (classes . ix (_unId i) . parents)
  ifor_ p \pNode pClass -> do
    share . at pNode .= Nothing
    pNode' <- canonicalize pNode
    pClass' <- findBee pClass
    share . at pNode' .= Just pClass'
  newParents <- executingStateT mempty $ ifor_ p \pNode pClass -> do
    pNode' <- lift $ canonicalize pNode
    isNew <- use (at pNode')
    whenJust isNew (void . lift . unionBee pClass)
    pClass' <- lift $ findBee pClass
    at pNode' .= Just pClass'
  classes . ix (_unId i) . parents .= newParents

-- ────────────────────────────── Extraction ─────────────────────────────── --
type Weighted f a = Cofree f a

astDepth :: Foldable f => f Natural -> Natural
astDepth f = maximum f + 1

astSize :: Foldable f => f Natural -> Natural
astSize f = sum f + 1

data Extractor f a = Extractor
  { _exShapes :: !(Set (f Id)),
    _minTree :: Maybe (Weighted f (a, Id))
  }

makeLenses ''Extractor

fixpoint :: Monad m => (a -> AccumT Any m a) -> a -> m a
fixpoint f x = do
  (out, changed) <- runAccumT (f x) (Any False)
  if getAny changed
    then fixpoint f out
    else pure out

extractBee :: forall f a. (Language f, Ord a) => (f a -> a) -> BG f (IntMap (Weighted f (a, Id)))
extractBee weigh = do
  rebuild
  cl <- use classes
  let exGraph = fmap (\n -> Extractor (n ^. shapes) Nothing) cl
  let f = executingState exGraph (fixpoint (const propagate) ())
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
      ifor_ map' \i node -> for_ (node ^. exShapes) \shape -> do
        s'' <- traverse (lift . use . at . _unId) shape
        whenJust (sequence s'') \s' ->
          whenJust (traverse _minTree s') \s ->
            update ((weigh (fmap (fst . extract) s), Id i) :< s) node (Id i)

-- ──────────────────────────────── Queries ──────────────────────────────── --
submapBetween :: Ord k => (k, k) -> Map k a -> Map k a
submapBetween (l, h) m = center
  where
    (_less, l', greaterEq) = Map.splitLookup l m
    (eq, h', _greater) = Map.splitLookup h greaterEq
    center = maybe id (Map.insert l) l' $ maybe id (Map.insert h) h' eq

-- Int should be read to always be positive
data Step
  = Step
  | Leap Int

data Leaper a
  = End
  | Continue Int a (Step -> Leaper a)
  deriving (Functor)

instance Foldable Leaper where
  foldMap _ End = mempty
  foldMap f (Continue _ a k) = f a <> foldMap f (k Step)

instance Applicative Leaper where
  pure a = go 0
    where
      go n = Continue n a \case
        Step -> go (n + 1)
        Leap i -> go i

  End <*> _ = End
  _ <*> End = End
  Continue a b c <*> Continue d e f = case compare a d of
    LT -> c (Leap d) <*> Continue d e f
    EQ -> Continue a (b e) \step -> c step <*> Continue d e f
    GT -> Continue a b c <*> f (Leap a)

instance Alternative Leaper where
  empty = End
  End <|> a = a
  a <|> End = a
  Continue a b c <|> Continue d e f = case compare a d of
    LT -> Continue a b \case
      Step -> c Step <|> Continue d e f
      Leap n -> c (Leap n) <|> f (Leap n)
    EQ -> Continue a b \case
      Step -> Continue d e f <|> c Step
      Leap n -> c (Leap n) <|> f (Leap n)
    GT -> Continue d e \case
      Step -> c Step <|> Continue d e f
      Leap n -> c (Leap n) <|> f (Leap n)

{-
  key(&self) -> Maybe<Key>
  next(&mut self)
  leap(&mut self, Key)
-}
-- data Leaper s = Leaper
--   { _key :: ST s (Maybe Int),
--     _next :: Step -> ST s ()
--   }

-- makeLenses ''Leaper

-- nats :: ST s (Leaper s)
-- nats = go <$> newSTRef 0
--   where
--     go ref = Leaper (Just <$> readSTRef ref) \case
--       Next -> do
--         modifySTRef ref (+ 1)
--       Leap m -> do
--         writeSTRef ref m

-- take10 :: (forall s. ST s (Leaper s)) -> [Int]
-- take10 l = runST (go 10 =<< l)
--   where
--     go :: Int -> Leaper s -> ST s [Int]
--     go 0 _ = pure []
--     go n l = do
--       k <- l ^. key
--       case k of
--         Nothing -> pure []
--         Just s -> do
--           l ^. next $ Next
--           ss <- go (n - 1) l
--           pure (s : ss)

-- leapfrog :: [Leaper s] -> ST s (Leaper s)
-- leapfrog ls = do
--   keys <- traverse (^. key) ls
--   case sequence keys of
--     Nothing -> pure $ Leaper (pure Nothing) (\_ -> pure ())
--     Just ks -> do
--       let list = map snd $ sortOn fst $ zip ks ls
--       array <- newListArray (0, length list) list
--       p <- newSTRef 0
--       go array p
--   where
--     go :: STArray s Int (Leaper s) -> STRef s Int -> ST s (Leaper s)
--     go = _

--     leapfrogSearch :: STArray s Int (Leaper s) -> STRef s Int -> ST s (Maybe Int)
--     leapfrogSearch = do

-- data Leaper a
--   = End
--   | Continue Int a (Step -> Leaper a)
--   deriving (Functor)

-- instance Filterable Leaper where
--   mapMaybe _ End = End
--   mapMaybe f (Continue i a g) = case f a of
--     Nothing -> mapMaybe f (g Next)
--     Just b -> Continue i b (mapMaybe f . g)

-- instance Foldable Leaper where
--   foldMap _ End = mempty
--   foldMap f (Continue _ a g) = f a <> foldMap f (g Next)

-- nats :: Leaper Int
-- nats = go 0
--   where
--     go n = Continue n n \case
--       Leap v -> go v
--       Next -> go (n + 1)

-- leapfrog :: Leaper a -> Leaper b -> Leaper (a, b)
-- leapfrog End _ = End
-- leapfrog _ End = End
-- leapfrog (Continue i a f) (Continue j b g) = go (i, a, f) (j, b, g)
--   where
--     mapContinue :: ((Int, a, Step -> Leaper a) -> Leaper b) -> Leaper a -> Leaper b
--     mapContinue _ End = End
--     mapContinue h (Continue x y z) = h (x, y, z)

--     go :: (Int, a, Step -> Leaper a) -> (Int, b, Step -> Leaper b) -> Leaper (a, b)
--     go (gi, ga, gf) (gj, gb, gg) =
--       case compare gi gj of
--         EQ -> Continue gi (ga, gb) $ mapContinue (`go` (gj, gb, gg)) . gf
--         LT -> mapContinue (`go` (gj, gb, gg)) (gf (Leap gj))
--         GT -> mapContinue ((gi, ga, gf) `go`) (gg (Leap gi))

-- data Shaped f a = Shaped (f a) a
--   deriving (Show, Functor, Foldable, Traversable)

-- termShape :: Shaped f a -> f a
-- termShape (Shaped f _) = f

-- data Jumper a
--   = Skip a
--   | Jumper (Leaper (Jumper a))
--   deriving (Functor)

-- abstract :: Jumper a -> Leaper (Jumper a)
-- abstract = \case
--   Skip _ -> End
--   Jumper le -> le

-- joinJumper :: Jumper a -> Jumper b -> Jumper (a, b)
-- joinJumper (Skip a) (Skip b) = Skip (a, b)
-- joinJumper (Jumper l) (Skip b) = fmap (,b) (Jumper l)
-- joinJumper (Skip a) (Jumper m) = fmap (a,) (Jumper m)
-- joinJumper (Jumper l) (Jumper m) = Jumper $ fmap (uncurry joinJumper) (leapfrog l m)

-- queryByShape :: forall f. Language f => f () -> BG f (Jumper (Shaped f Id))
-- queryByShape f = do
--   m <- submapBetween (f $> Id minBound, f $> Id maxBound) <$> use share
--   pure $ Jumper $ go 0 m
--   where
--     go :: Int -> Map (f Id) Id -> Leaper (Jumper (Shaped f Id))
--     go depth m = fromMaybe End do
--       ((f', i'), m') <- Map.minViewWithKey m
--       let s = Shaped f' i'
--       i <- s ^? traversed . index depth
--       let sub =
--             if isJust (s ^? traversed . index (depth + 1))
--               then Jumper (go (depth + 1) (submapBetween (mini, maxi) m))
--               else Skip s
--           mini = termShape $ s & traversed . indices (> depth) .~ minBound
--           maxi = termShape $ s & traversed . indices (> depth) .~ maxBound
--           mWithout Next = maxi
--           mWithout (Leap n) = max maxi (termShape $ s & traversed . index depth .~ Id n)
--           mWithoutSub leap = dropWhileAntitone (<= mWithout leap) m'
--        in pure $ Continue (_unId i) sub (go depth . mWithoutSub)

-- triewalk :: Jumper a -> [a]
-- triewalk (Skip a) = [a]
-- triewalk (Jumper c) = concat $ go c
--   where
--     go End = []
--     go (Continue _ l f) = triewalk l : go (f Next)

-- ───────────────────────────── Test language ───────────────────────────── --
data Foo a
  = H a a
  | G Int
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Foo a)

instance Language Foo

instance Show1 Foo where
  liftShowsPrec sp sl p (H a b) = showsBinaryWith sp sp "F" p a b
  liftShowsPrec sp sl p (G i) = showsUnaryWith showsPrec "G" p i

-- test :: String
-- test = show $
--   evaluatingState emptyBee $ do
--     g0 <- insertBee (G 0)
--     g1 <- insertBee (G 1)
--     g2 <- insertBee (G 2)
--     g3 <- insertBee (G 3)
--     f1 <- insertBee (H g0 g1)
--     f2 <- insertBee (H f1 g1)
--     f3 <- insertBee (H f2 g1)
--     f4 <- insertBee (H f3 g1)
--     rebuild
--     hxya <- queryByShape (H () ())
--     ga <- queryByShape (G 1)
--     let s = abstract <$> abstract hxya
--     let y = fmap (fmap \j -> hxya `joinJumper` hxya) s
--     pure (triewalk hxya) --(Jumper (fmap Jumper y)))
