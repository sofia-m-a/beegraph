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
    Shaped (..),
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens hiding ((:<), (<.>))
import Control.Monad.Free (Free, MonadFree (wrap), iterA)
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Foldable (maximum)
import Data.Functor.Classes (Show1 (liftShowsPrec), showsBinaryWith, showsUnaryWith)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.Traversable (for)
import GHC.Exts qualified as Ext
import GHC.Show (Show (showsPrec))
import Relation
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
data Shaped f a = Shaped (f a) a
  deriving (Show, Functor, Foldable, Traversable)

termShape :: Lens' (Shaped f a) (f a)
termShape = lens (\(Shaped f _) -> f) (\(Shaped _ k) g -> Shaped g k)

submapBetween :: Ord k => (k, k) -> Map k a -> Map k a
submapBetween (l, h) m = center
  where
    (_less, l', greaterEq) = Map.splitLookup l m
    (eq, h', _greater) = Map.splitLookup h greaterEq
    center = maybe id (Map.insert l) l' $ maybe id (Map.insert h) h' eq

queryByShape :: forall f. Language f => f () -> BG f Nary
queryByShape s = queryBetween (s $> minBound, s $> maxBound) (length s)

queryBetween :: forall f. Language f => (f Id, f Id) -> Int -> BG f Nary
queryBetween bounds limit = use share <&> go 0 . submapBetween bounds
  where
    go :: Int -> Map (f Id) Id -> Nary
    go depth _ | depth > limit = Never
    go depth m =
      let l = rel depth m
       in Nary (fromList (map fst l)) (\i -> maybe Never (go (depth + 1)) (Map.fromList l ^? ix i))

    rel depth m =
      Map.toAscList m
        & mapMaybe
          ( (\(a, b) -> (,b) <$> a)
              . ( preview (traversed . index depth . unId)
                    &&& \s ->
                      submapBetween
                        ( view termShape (s & traversed . indices (> depth) .~ minBound),
                          view termShape (s & traversed . indices (> depth) .~ maxBound)
                        )
                        m
                )
              . uncurry Shaped
          )

equ :: Nary
equ = Nary [0 .. 8] (\i -> Nary [i] (const Never))

newtype Var = Var {_unVar :: Word} deriving (Eq, Ord, Show)

makeLenses ''Var

data Stream a = a :& Stream a deriving (Functor)

infixr 5 :&

vars :: Stream Var
vars = fmap Var (go 0)
  where
    go n = n :& go (n + 1)

type Equ = (Var, Var)

data Matcher f = Matcher
  { _atoms :: [([Var], BG f Nary)]
  }

runMatcher :: Matcher f -> BG f Nary
runMatcher (Matcher atoms) = do
  atoms' <- traverse (\(vs, f) -> (vs,) <$> f) atoms
  let vars' = setOf (folded . _1 . folded) atoms'
  pure $ go vars' atoms'
  where
    go :: Set Var -> [([Var], Nary)] -> Nary
    go vs xs = case Set.minView vs of
      Nothing -> Never
      Just (v, vs') ->
        let rels = xs ^.. folded . filtered (\x -> (x ^? _1 . _head) == Just v) . _2 . _Nary . _1
            joined = conjoin rels
            update i =
              xs <&> \(us, n) -> case us ^? _Cons of
                Just (u, us')
                  | u == v ->
                    ( us',
                      case n of
                        Never -> Never
                        Nary _ k -> k i
                    )
                _ -> (us, n)
         in Nary joined (go vs' . update)

matcher :: Language f => Free f Var -> (Matcher f, Var)
matcher lhs =
  let freshVar = Var $ maybe 0 (+ 1) $ maximumOf (traverse . unVar) lhs
      (lhsHead, (equs, _freshVar', flattenedLHS)) = usingState (mempty :: Set Equ, freshVar, [] :: [Shaped f Var]) $ flip iterA lhs \f -> do
        flatF <- sequence f
        flatF' <- evaluatingStateT Nothing $ for flatF \v -> do
          prev <- get
          if
              | Just u <- prev,
                v <= u -> do
                var' <- lift $ use _2
                lift $ _2 . unVar += 1
                lift (_1 . at (v, var') .= Just ())
                put (Just var')
                pure var'
              | otherwise -> put (Just v) >> pure v
        var <- use _2
        _2 . unVar += 1
        let sh = Shaped flatF' var
        _3 %= cons sh
        pure var
      atoms = fmap (toList &&& queryByShape . void . view termShape) flattenedLHS ++ fmap (\(a, b) -> ([a, b], pure equ)) (toList equs)
   in (Matcher atoms, lhsHead)

data Rewrite f = Rewrite
  { _lhs :: Matcher f,
    _lhsHead :: Var,
    _rhs :: Free f Var
  }

(~>) :: Language f => Free f Var -> Free f Var -> Rewrite f
(~>) lhs rhs = Rewrite m h rhs where (m, h) = matcher lhs

-- ────────────────────────── Equality saturation ────────────────────────── --
-- saturate :: forall f. Language f => BG f (Jumper (Shaped f Id)) -> BG f ()
-- saturate query = fixpoint (const go) ()
--   where
--     go :: AccumT Any (State (Beegraph f)) ()
--     go = do
--       j <- lift query
--       for_ j \(Shaped f i) -> do
--         new <- lift $ insertBee f
--         _ <- lift $ unionBee new i
--         add (Any True)

-- ───────────────────────────── Test language ───────────────────────────── --
data Foo a
  = H a a
  | J a
  | G Int
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

makePrisms ''Foo

instance Language Foo

instance Show1 Foo where
  liftShowsPrec sp sl p (H a b) = showsBinaryWith sp sp "H" p a b
  liftShowsPrec sp sl p (J a) = showsUnaryWith sp "J" p a
  liftShowsPrec sp sl p (G i) = showsUnaryWith showsPrec "G" p i

test :: String
test = id $
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
    j0 <- insertBee (J g0)
    j1 <- insertBee (J g1)
    j2 <- insertBee (J g2)
    j3 <- insertBee (J j2)
    rebuild
    let (a :& b :& c :& _) = fmap pure vars
    let (m, _) = matcher (wrap (H (wrap $ H a b) c))
    nary <- runMatcher m
    pure (debugTree nary)

foo :: [[Word]]
foo = fmap (fmap _unVar) $ map fst $ _atoms $ fst m
  where
    (a :& b :& c :& _) = fmap pure vars
    m = matcher (wrap (H (wrap $ H a b) c))