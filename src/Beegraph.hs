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
    (~>),
    vars,
    Shaped (..),
    Rewrite,
    saturate,
    Stream (..),
  )
where

import Control.Comonad (Comonad (extract))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens hiding ((:<), (<.>))
import Control.Monad.Free (Free, MonadFree (wrap), iterA)
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Foldable (Foldable (foldr1), maximum, maximumBy)
import Data.Functor.Classes (Show1 (liftShowsPrec), showsBinaryWith, showsUnaryWith)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.Traversable (for)
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
data Shaped f a = Shaped {
  _termShape :: f a,
  _termName :: a
  }
  deriving (Show, Functor, Foldable, Traversable)

makeLenses ''Shaped

submapBetween :: Ord k => (k, k) -> Map k a -> Map k a
submapBetween (l, h) m = center
  where
    (_less, l', greaterEq) = Map.splitLookup l m
    (eq, h', _greater) = Map.splitLookup h greaterEq
    center = maybe id (Map.insert l) l' $ maybe id (Map.insert h) h' eq

newtype Var = Var {_unVar :: Word} deriving (Eq, Ord, Show)

makeLenses ''Var

data Stream a = a :& Stream a deriving (Functor)

infixr 5 :&

vars :: Stream Var
vars = fmap Var (go 0)
  where
    go n = n :& go (n + 1)

queryByShape :: forall f. Language f => Shaped f Var -> BG f Rel
queryByShape f = query ((f ^. termShape) $> minBound, (f ^. termShape) $> maxBound) f

query :: forall f. Language f => (f Id, f Id) -> Shaped f Var -> BG f Rel
query (a, b) f = use share <&> ifoldr go Null . submapBetween (a, b)
  where
    go :: f Id -> Id -> Rel -> Rel
    go k v r =
      let shaped = Shaped k v
          zipped = zip (toList shaped) (toList f)
          sorted = sortOn snd zipped
          dedup ((i, a') : (j, b') : xs) | a' == b' = if i == j then dedup ((j, b') : xs) else Nothing
          dedup ((i, a') : xs) = ((i, a') :) <$> dedup xs
          dedup [] = Just []
          dedupped = dedup sorted
          insert [] rel = rel
          insert (x : xs) Null = Nary (fromList [(x, insert xs Null)])
          insert (x : xs) (Nary m) = Nary $ Map.insert x (insert xs (fromMaybe Null $ Map.lookup x m)) m
       in maybe r (\xs -> insert (fmap (^. _1 . unId) xs) r) dedupped

data Matcher f = Matcher
  {
    _atoms :: [([Var], BG f Rel)],
    _matchKeep :: [Bool]
  }

makeLenses ''Matcher

matcher :: Language f => Free f Var -> (Matcher f, Var)
matcher lhs = (Matcher atoms' keep,  lhsHead)
  where
    freshVar = Var $ maybe 0 (+ 1) $ maximumOf folded $ fmap (^. unVar) lhs
    (lhsHead, (_freshVar', atoms')) = usingState (freshVar, []) $ flip iterA lhs \f -> do  
      seq <- sequence f
      _2 <>= foldMap (const []) seq
      var <- use _1
      _1 . unVar += 1
      let f = Shaped seq var
      _2 %= cons (toList f, queryByShape f)
      pure var
    keep = (toList lhs $> True) ++ ([freshVar ^. unVar .. lhsHead ^. unVar - 1] $> False) ++ [True]

runMatcher :: Matcher f -> BG f Rel
runMatcher (Matcher atoms' _) = do
  atoms'' <- traverse (\(vs, f) -> (vs,) <$> f) atoms'
  let vars' = setOf (folded . _1 . folded) atoms''
  pure $ go vars' (atoms'' <&> _1 %~ fromList)
  where
    go :: Set Var -> [(Set Var, Rel)] -> Rel
    go vs xs = case Set.minView vs of
      Nothing -> Null
      Just (v, vs') ->
        let rels = xs ^.. folded . filtered (\x -> (x ^. _1 . to Set.lookupMin) == Just v) . _2 . _Nary
            joined = maybe mempty Map.keys (foldr1 Map.intersection <$> nonEmpty rels)
            update i =
              xs <&> \(us, n) -> case Set.minView us of
                Just (u, us')
                  | u == v ->
                    ( us',
                      case n of
                        Null -> Null
                        Nary m -> fromMaybe Null $ Map.lookup i m
                    )
                _ -> (us, n)
         in Nary (fromList $ (\i -> (i, go vs' (update i))) <$> joined)

extractMatcher :: forall b. Ord b => Rel -> [Bool] -> ([Int] -> Maybe b) -> Set b
extractMatcher r v o = go [] v r
  where
    go :: [Int] -> [Bool] -> Rel -> Set b
    go ss [] Null = maybe mempty Set.singleton (o $ reverse ss)
    go _ss _ Null = mempty
    go _ss [] (Nary _) = mempty
    go ss (False : bs) (Nary m) = ifoldMap (\_i re -> go ss bs re) m
    go ss (True : bs) (Nary m) = ifoldMap (\i re -> go (i : ss) bs re) m

data Rewrite f = Rewrite
  { _lhs :: Matcher f,
    _lhsHead :: Var,
    _rhs :: Free f Var
  }

makeLenses ''Rewrite

(~>) :: Language f => Free f Var -> Free f Var -> Rewrite f
(~>) lhs = Rewrite m h where (m, h) = matcher lhs

runRewrite :: (Show (f Id), Language f) => Rel -> Var -> [Bool] -> Free f Var -> AccumT Any (State (Beegraph f)) ()
runRewrite rel lhsHead keep rhs = do
  let rvars = toListOf folded rhs ++ [lhsHead]
  let results = extractMatcher rel keep (Just . Map.fromList . zip rvars)
  for_ results \result -> do
    let substituted = for rhs (`Map.lookup` result)
    let ltop = Map.lookup lhsHead result
    for_ (liftA2 (,) substituted ltop) \(subs, ltop') -> do
      rtop <- iterA (sequence >=> (lift . insertBee)) (fmap Id subs)
      (l', r') <- liftA2 (,) (lift $ findBee $ Id ltop') (lift $ findBee rtop)
      when (l' /= r') do
        _ <- lift $ unionBee l' r'
        add (Any True)

-- ────────────────────────── Equality saturation ────────────────────────── --
saturate :: forall f. (Show (f Id), Language f) => [Rewrite f] -> BG f ()
saturate rws =
  fixpoint
    ( const $ do
        -- get matches
        rels <- lift $ traverse (runMatcher . view lhs) rws
        -- apply substitution
        zipWithM_ (\rel rw -> runRewrite rel (rw ^. lhsHead) (rw ^. lhs . matchKeep) (rw ^. rhs)) rels rws
        -- rebuild
        lift rebuild
    )
    ()