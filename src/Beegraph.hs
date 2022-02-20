{-# LANGUAGE FlexibleContexts #-}
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
    -- todo
    (~>),
    vars,
    queryByShape,
    Leaper,
    Jumper,
    Shaped (..),
    equ,
    saturate,
    exists,
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens hiding ((:<), (<.>))
import Control.Monad.Free (Free (Free, Pure), MonadFree (wrap), iterA)
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Foldable (maximum)
import Data.Functor.Classes (Show1 (liftShowsPrec), showsBinaryWith, showsUnaryWith)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Traversable (for)
import GHC.Exts qualified
import GHC.Show (Show (showsPrec))
import Witherable (mapMaybe)
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
      Step -> Continue a b c <|> f Step
      Leap n -> c (Leap n) <|> f (Leap n)

instance IsList (Leaper a) where
  type Item (Leaper a) = a
  fromList :: [a] -> Leaper a
  fromList = go 0
    where
      go _ [] = End
      go n (s : ss) = Continue n s \case
        Step -> go (n + 1) ss
        Leap m -> go m $ drop (m - n) ss
  toList = toList

equ :: Leaper (Leaper ())
equ = go 0
  where
    go n = Continue n (Continue n () (const End)) \case
      Step -> go (n + 1)
      Leap m -> go m

data Shaped f a = Shaped (f a) a
  deriving (Show, Functor, Foldable, Traversable)

termShape :: Lens' (Shaped f a) (f a)
termShape = lens (\(Shaped f _) -> f) (\(Shaped _ k) g -> Shaped g k)

type Jumper a = Free Leaper a

queryByShape :: forall f a. Language f => ATraversal' (f Id) a -> f () -> BG f (Jumper (a, Id))
queryByShape tr f = queryBetween (f $> Id 0, f $> Id maxBound) (length f) tr

queryBetween :: forall f a. Language f => (f Id, f Id) -> Int -> ATraversal' (f Id) a -> BG f (Jumper (a, Id))
queryBetween bounds depth tr = do
  m <- submapBetween bounds <$> use share
  pure $ go 0 depth m
  where
    tr' = cloneTraversal tr

    go :: Int -> Int -> Map (f Id) Id -> Jumper (a, Id)
    go depth limit m = fromMaybe (wrap End) do
      (k, v) <- Map.lookupMin m
      let s = Shaped k v
          here :: (Indexable Int p, Traversable f1, Applicative f2) => p b (f2 b) -> f1 b -> f2 (f1 b)
          here = traversed . index depth
          (submap, rest) = Map.spanAntitone (\g -> (g ^? here) == (k ^? here)) m
      i <- s ^? here
      pure $
        if depth + 1 == limit
          then -- the wrap End case shouldn't happen for a valid Traversal'/shape combo
            maybe (wrap End) (pure . (,v)) (k ^? tr')
          else
            wrap
              ( Continue (_unId i) (go (depth + 1) limit submap) \case
                  Step -> exists $ go depth limit rest
                  Leap n -> exists $ go depth limit (Map.dropWhileAntitone (\y -> y ^? here . unId < Just n) rest)
              )

exists :: Jumper a -> Leaper (Jumper a)
exists = \case
  Pure _ -> End
  Free le -> le

triewalk :: Jumper a -> [a]
triewalk (Pure a) = [a]
triewalk (Free c) = concat $ go c
  where
    go End = []
    go (Continue _ l f) = triewalk l : go (f Step)

newtype Var = Var {_unVar :: Word} deriving (Eq, Ord, Show)

makeLenses ''Var

vars :: [Var]
vars = map Var [0 ..]

type Equ = (Var, Var)

data Rewrite f = Rewrite
  { _lhs :: [Shaped f Var],
    _lhsEqus :: Set (Var, Var),
    _lhsHead :: Var,
    _rhs :: Free f Var
  }

(~>) :: Language f => Free f Var -> Free f Var -> Rewrite f
(~>) lhs rhs =
  let freshVar = Var $ maybe 0 (+ 1) $ maximumOf (traverse . unVar) lhs
      (linearLHS, (_, equs, freshVar')) = usingState (mempty :: Set Var, mempty :: Set Equ, freshVar) $ for lhs \var -> do
        b <- use (_1 . contains var)
        if b
          then do
            fresh <- use _3
            _2 . at (var, fresh) .= Just ()
            _3 . unVar += 1
            pure fresh
          else do
            _1 . at var .= Just ()
            pure var
      (lhsHead, (flattenedLHS, _freshVar'')) = usingState ([], freshVar') $ flip iterA linearLHS \f -> do
        flatF <- sequence f
        var <- use _2
        _2 . unVar += 1
        _1 %= cons (Shaped flatF var)
        pure var
   in Rewrite flattenedLHS equs lhsHead rhs

joinList :: [Jumper a] -> Jumper [a]
joinList = sequence

-- runRewrite :: Language f => Rewrite f -> BG f ()
-- runRewrite (Rewrite lhs equs head rhs) = do
--   _

{-
  (x, y, z) <-
  F (G x) (H (F y) z)
  -->
  F a b, c; G x, a; H d z, b; F y, d;

 -}

-- ────────────────────────── Equality saturation ────────────────────────── --
saturate :: forall f. Language f => BG f (Jumper (Shaped f Id)) -> BG f ()
saturate query = fixpoint (const go) ()
  where
    go :: AccumT Any (State (Beegraph f)) ()
    go = do
      j <- lift query
      for_ j \(Shaped f i) -> do
        new <- lift $ insertBee f
        _ <- lift $ unionBee new i
        add (Any True)

-- ───────────────────────────── Test language ───────────────────────────── --
data Foo a
  = H a a
  | G Int
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

makePrisms ''Foo

instance Language Foo

instance Show1 Foo where
  liftShowsPrec sp sl p (H a b) = showsBinaryWith sp sp "H" p a b
  liftShowsPrec sp sl p (G i) = showsUnaryWith showsPrec "G" p i

test :: String
test = show $
  evaluatingState emptyBee $ do
    g0 <- insertBee (G 0)
    g1 <- insertBee (G 1)
    g2 <- insertBee (G 2)
    g3 <- insertBee (G 3)
    f1 <- insertBee (H g0 g1)
    f2 <- insertBee (H f1 g1)
    f3 <- insertBee (H f2 g1)
    f4 <- insertBee (H f3 g1)
    f5 <- insertBee (H g3 g3)
    rebuild
    habx <- queryByShape _H (H () ())
    g0q <- queryByShape _G (G 3)
    let s = wrap $ liftA2 const (exists habx) (exists g0q)
    pure (triewalk s)