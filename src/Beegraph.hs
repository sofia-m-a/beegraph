{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Beegraph
  ( Language,
    type Id,
    unId,
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
    Shaped(..),
    Var,
    Query(..),
    queryTree,
    wildcard,
    runQuery,
    (~>),
    Rewrite,
    saturate,
    debugclass
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens hiding ((:<), (<.>))
import Control.Monad.Free (Free (Pure, Free), iterA)
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Deriving (deriveShow1)
import Data.Foldable (maximum)
import Data.Functor.Classes (Show1, showsUnaryWith, showsPrec1)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import GHC.Show (Show (showsPrec))
import Relation
import Witherable (mapMaybe)
import Prelude hiding (mapMaybe)
import qualified GHC.Exts as Ext
import Data.Traversable (for)
import qualified Data.IntSet.Lens as IntSet
import qualified Data.Set as Set
import qualified Data.Set.Lens as Set
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
  deriving (Show)

makeLenses ''Node

-- ─────────────────────────────── Beeclass ──────────────────────────────── --
type BeeNode f = f Id

data Beeclass f = Beeclass
  { _shapes :: !(Set (BeeNode f)),
    _parents :: !(Seq (BeeNode f, Id))
  }

makeLenses ''Beeclass

instance Language f => Semigroup (Beeclass f) where
  Beeclass s p <> Beeclass t q = Beeclass (s <> t) (p <> q)

debugclass :: Show (f Id) => Beeclass f -> String
debugclass (Beeclass s p) = show s <> " & p: " <> show p

-- ─────────────────────────────── Beegraph ──────────────────────────────── --
data Beegraph f = Beegraph
  { -- union find: equivalence relation over beenode-IDs
    _nodes :: !(IntMap (Node f)),
    -- maps beenode-IDs to beeclasses
    _classes :: !(IntMap (Beeclass f)),
    -- maps shapes to IDs
    _share :: !(Map (BeeNode f) Id),
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
findBee :: Language f => Id -> BG f Id
findBee = ufFind

canonicalize :: Language f => f Id -> BG f (f Id)
canonicalize = traverse findBee

insertBee :: Language f => f Id -> BG f Id
insertBee f = do
  g <- canonicalize f
  m <- use (share . at g)
  j <- whenNothing m do
    i <- ufInsert
    share . at g .= Just i
    classes . at (_unId i) .= Just (Beeclass (one g) mempty)
    for_ g \j -> classes . ix (_unId j) . parents <>= one (g, i)
    pure i
  findBee j

unionBee :: Language f => Id -> Id -> BG f (Maybe Id)
unionBee a b = do
  u <- ufUnion a b
  case u of
      Just u' -> do
        pa <- use (classes . at (a ^. unId))
        pb <- use (classes . at (b ^. unId))
        let p = pa <> pb
        classes . at (a ^. unId) .= Nothing
        classes . at (b ^. unId) .= Nothing
        classes . at (u' ^. unId) .= p
        worklist <>= one (u' ^. unId)
        pure (Just u')
      Nothing -> pure Nothing

rebuild :: (Show (f Id), Language f) => BG f ()
rebuild = do
  w <- use worklist
  when (IntSet.size w /= 0) do
    worklist .= mempty
    todo :: IntSet <- fmap (fromList . fmap _unId) . traverse (findBee . Id) . IntSet.toList $ w
    forOf_ IntSet.members todo (repair . Id)
    rebuild

repair :: forall f. Language f => Id -> BG f ()
repair i = do
  p <- use (classes . ix (_unId i) . parents)
  for_ p \(pNode, pClass) -> do
    share . at pNode .= Nothing
    pNode' <- canonicalize pNode
    pClass' <- findBee pClass
    share . at pNode' .= Just pClass'
  newParents <- executingStateT mempty $ for_ p \(pNode, pClass) -> do
    pNode' <- lift $ canonicalize pNode
    isNew <- use (at pNode')
    whenJust isNew (void . lift . unionBee pClass)
    pClass' <- lift $ findBee pClass
    at pNode' .= Just pClass'
  classes . ix (_unId i) . parents .= fromList (Map.toList newParents)

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

extractBee :: forall f a. (Show (f Id), Language f, Ord a) => (f a -> a) -> BG f (IntMap (Weighted f (a, Id)))
extractBee weigh = do
  rebuild
  cl <- use classes
  exGraph <- for cl \n -> do
    n' <- fromList <$> traverse canonicalize (toList (n ^. shapes))
    pure $ Extractor n' Nothing
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
data Shaped f a = Shaped {
  _termShape :: f a,
  _termName :: a
  }
  deriving (Functor, Foldable, Traversable)

makeLenses ''Shaped

deriveShow1 ''Shaped

instance (Show1 f, Show a) => Show (Shaped f a) where showsPrec = showsPrec1

type Var = Word

data Query f
  = QueryVar Var
  | QueryShaped (Shaped f Var)
  | QueryJoin Word [Query f]
  deriving (Show)

queryTree :: forall f. Language f => Free f Word -> (Var, Query f)
queryTree f = second optimize $ evaluatingState freshVar $ go f
  where
    freshVar = maybe 0 (1 +) $ maximumOf folded f

    go (Pure w) = pure (w, QueryVar w)
    go (Free f') = do
      f'' <- traverse go f'
      h <- id <<+= 1
      pure (h, foldr (\(j, q) p -> QueryJoin j [q, p]) (QueryShaped $ Shaped (fmap fst f'') h) (toList f''))

    optimize :: Query f -> Query f
    optimize (QueryJoin w [QueryVar w', x]) | w == w' = optimize x
    optimize (QueryJoin k ss) = QueryJoin k (fmap optimize ss)
    optimize q = q

submapBetween :: Ord k => (k, k) -> Map k a -> Map k a
submapBetween (l, h) m = center
  where
    (_less, l', greaterEq) = Map.splitLookup l m
    (eq, h', _greater) = Map.splitLookup h greaterEq
    center = maybe id (Map.insert l) l' $ maybe id (Map.insert h) h' eq

wildcard :: BG f Rel
wildcard = use share <&> (Map.elems >>> fmap (^. unId) >>> sort >>> fromList)

runQuery :: forall f. Language f => Rel -> Query f -> BG f (Nary Var)
-- a unary relation. We take a pre-calculated wildcard Rel in as an optimization
runQuery i (QueryVar w) = pure $ Nary w i (const Nullary)
runQuery _ (QueryShaped sh) = do
  s <- use share
  -- first, split off the submap containing things of valid shape
  let s' = submapBetween (sh ^. termShape $> minBound, sh ^. termShape $> maxBound) s
  pure $ toNary $ ifoldr go SetNullary s'
  where
    -- then group each Id with the variable it corresponds to,
    -- and sort by the variables
    -- and insert into the n-ary relation
    go :: f Id -> Id -> SetNary Var -> SetNary Var
    go f i n = foldr (\(v, Id i) -> setInsert v i) n $ sortOn fst $ zip (toList sh) (toList (Shaped f i))
runQuery i (QueryJoin w qs) = do
  qs' <- traverse (runQuery i) qs
  pure $ go qs' []
  where
    go :: [Nary Var] -> [(Rel, Int -> Nary Var)] -> Nary Var
    go [] ls = Nary w (conjoin (fmap fst ls)) (\i -> go (fmap (\(_, k) -> k i) ls) [])
    go (Nullary:_ns) _ls = Nullary
    go (Nary v rel k:ns) ls = if v == w
      then go ns ((rel, k):ls)
      else Nary v rel (\i -> go (k i:ns) ls)

data Rewrite f = Rewrite
  {
    _query :: Query f,
    _pivot :: Var,
    _target :: Free f Var
  }

makeLenses ''Rewrite

(~>) :: Language f => Free f Var -> Free f Var -> Rewrite f
(~>) lhs = Rewrite q v where (v, q) = queryTree lhs

extractNary :: Nary Var -> [Map Var Int]
extractNary Nullary = [mempty]
extractNary (Nary v rel k) = do
  i <- Ext.toList rel
  m <- extractNary (k i)
  pure (one (v, i) <> m)

runRewrite :: (Show1 f, Show (f Id), Language f) => Nary Var -> Free f Var -> Var -> AccumT Any (State (Beegraph f)) ()
runRewrite nary target pivot =
  for_ (extractNary nary) \m -> do
    let substituted = for target (`Map.lookup` m)
    let pivot' = pivot `Map.lookup` m
    traceM $ "map: " <> show m <> ", subs: " <> show substituted <> ", pivot" <> show pivot'
    for_ (liftA2 (,) substituted pivot') \(subs, p) -> do
      top <- iterA (sequence >=> (lift . insertBee)) (fmap Id subs)
      (l', r') <- liftA2 (,) (lift $ findBee $ Id p) (lift $ findBee top)
      when (l' /= r') do
        _ <- lift $ unionBee l' r'
        add (Any True)

-- ────────────────────────── Equality saturation ────────────────────────── --
saturate :: forall f. (Show1 f, Show (f Id), Language f) => [Rewrite f] -> BG f ()
saturate rws =
  fixpoint
    ( const $ do
        wc <- lift wildcard
        -- get matches
        rels <- lift $ traverse (runQuery wc . view query) rws
        -- apply substitution
        zipWithM_ (\rel rw -> runRewrite rel (rw ^. target) (rw ^. pivot)) rels rws
        -- rebuild
        lift rebuild
    )
    ()