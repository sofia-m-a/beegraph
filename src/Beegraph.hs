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
import Control.Comonad.Cofree (Cofree ((:<)), ComonadCofree (unwrap), coiter, _extract, _unwrap)
import Control.Comonad.Cofree qualified as Cofree
import Control.Lens hiding ((:<))
import Control.Monad.Free
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Data.Fix (Fix (Fix))
import Data.Foldable (maximum)
import Data.Functor.Combinator (Comp)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Sequence (Seq ((:<|), (:|>)))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Witherable (Witherable (wither), mapMaybe)
import Prelude hiding (mapMaybe)

class (Traversable f, Ord (f Id)) => Language f

type Id = Int

data Node f = Node
  { -- union-find fields
    _ufParent :: !Id,
    _ufRank :: !Word16,
    _shape :: !(f Id)
  }

makeLenses ''Node

type Watcher f = Free (Comp Maybe ((->) (f Id)))

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
    --watcher %= ($ Insert (j', i)) . unwrap

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
    --watcher %= ($ Union (a, a') (b, b')) . unwrap
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

submapBetween :: Ord k => (k, k) -> Map k a -> Map k a
submapBetween (l, h) m = eq
  where
    (_less, greaterEq) = Map.split l m
    (eq, _greater) = Map.split h greaterEq

queryByShape :: Language f => f () -> BG f i (Map (f Id) Id)
queryByShape shape' =
  submapBetween (shape' $> minBound, shape' $> maxBound) <$> use shapes

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

nats :: Int -> Int -> Leaper LeapVal
nats step offset =
  coiter
    ( \s -> \case
        Nothing -> case s of
          Some n -> Some $ n + step
          End -> End
        Just k -> case s of
          Some s' -> Some $ ((s' - offset) `div` step) * step + offset
          End -> End
    )
    (Some offset)

listy :: [Int] -> Leaper LeapVal
listy = Cofree.unfold \case
  [] -> (End, const [])
  s : ss ->
    ( Some s,
      \case
        Nothing -> ss
        Just (Some k) -> dropWhile (< k) ss
        Just End -> []
    )

show10 :: Leaper LeapVal -> [LeapVal]
show10 l = map extract $ take 10 $ iterate f l
  where
    f :: Leaper LeapVal -> Leaper LeapVal
    f s = unwrap s Nothing

test :: [LeapVal]
test = show10 $ triejoin [listy [0 .. 20], listy [2, 4, 6, 8, 10, 12], listy [3, 6, 9, 12, 15]]

data Foo a
  = F a a
  | G Int
  deriving (Eq, Ord, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Foo a)