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
import Control.Comonad.Cofree (Cofree ((:<)), coiter, _extract, _unwrap)
import Control.Lens hiding ((:<))
import Control.Monad.Free (Free)
import Control.Monad.Free.Church
import Control.Monad.Trans.Accum (AccumT, add, runAccumT)
import Control.Monad.Trans.Cont (ContT (ContT), evalContT)
import Data.Fix (Fix)
import Data.Foldable (maximum)
import Data.Functor.Classes (Show1 (liftShowsPrec), showsBinaryWith, showsUnaryWith)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map (dropWhileAntitone)
import Data.Map qualified as Map
import Data.Sequence (Seq ((:<|), (:|>)))
import Data.Traversable (for)
import GHC.Show (Show (showsPrec))
import Witherable (mapMaybe)
import Prelude hiding (mapMaybe)

class (Traversable f, Show (f Id), Ord (f Id), Hashable (f Id)) => Language f

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
    _parents :: !(Map (f Id) Id)
  }

deriving instance Language f => Show (Beeclass f)

makeLenses ''Beeclass

data Beegraph f = Beegraph
  { -- union find: equivalence relation over beeclass-IDs
    _nodes :: !(IntMap (Node f)),
    -- maps beeclass-IDS to beeclasses
    _classes :: !(IntMap (Beeclass f)),
    _share :: !(Map (f Id) Id),
    _worklist :: !IntSet
  }

makeLenses ''Beegraph

type BG f a = State (Beegraph f) a

emptyBee :: Language f => Beegraph f
emptyBee = Beegraph mempty mempty mempty mempty

parent :: Id -> Traversal' (Beegraph f) Id
parent i = nodes . ix (_unId i) . ufParent

-- union-find
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

-- Extraction
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
  graph <- get
  let exGraph = fmap (\n -> Extractor (n ^. shapes) Nothing) (graph ^. classes)
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

submapBetween :: Ord k => (k, k) -> Map k a -> Map k a
submapBetween (l, h) m = eq
  where
    (_less, greaterEq) = Map.split l m
    (eq, _greater) = Map.split h greaterEq

data Step
  = Next
  | Leap Int

data Leaper a
  = End
  | Continue Int a (Step -> Leaper a)

takeTheL :: Int -> Leaper a -> [(Int, a)]
takeTheL 0 _ = []
takeTheL _ End = []
takeTheL n (Continue s a f) = (s, a) : takeTheL (n - 1) (f Next)

gnuCatboy :: [Int] -> Leaper Int
gnuCatboy [] = End
gnuCatboy (s : ss) = Continue s s \case
  Next -> gnuCatboy ss
  Leap k -> gnuCatboy $ dropWhile (< k) ss

nats :: Leaper (Int, Int)
nats = go 0
  where
    go n = Continue n (n, n) \case
      Leap v -> go v
      Next -> go (n + 1)

leapfrog :: Leaper a -> Leaper b -> Leaper (a, b)
leapfrog End _ = End
leapfrog _ End = End
leapfrog (Continue i a f) (Continue j b g) = go (i, a, f) (j, b, g)
  where
    go :: (Int, a, Step -> Leaper a) -> (Int, b, Step -> Leaper b) -> Leaper (a, b)
    go (i, a, f) (j, b, g) =
      case compare i j of
        EQ -> Continue i (a, b) \step -> case f step of
          End -> End
          Continue i' a' f' -> go (i', a', f') (j, b, g)
        LT -> case f (Leap j) of
          End -> End
          Continue i' a' f' -> go (i', a', f') (j, b, g)
        GT -> case g (Leap i) of
          End -> End
          Continue j' b' g' -> go (i, a, f) (j', b', g')

-- data RingView a = RingView
--   { _mini :: a,
--     _seq :: Seq a,
--     _maxi :: a
--   }
--   deriving (Show, Functor, Foldable, Traversable)

-- makeLenses ''RingView

-- -- I swear these are exhaustive
-- rotateRingL :: RingView a -> RingView a
-- rotateRingL (RingView l m r) = case m of
--   Empty -> RingView r Empty l
--   l' :<| m' -> RingView l' (m' :|> r) l

-- leapfrog :: [Leaper] -> Leaper
-- leapfrog ls = case fromList . sortOn (view _1) <$> unending of
--   Nothing -> End
--   Just Empty -> End
--   Just ((k, f) :<| Empty) -> Continue k f
--   Just (l :<| (m :|> r)) -> go (RingView l m r)
--   where
--     unending :: Maybe [(Int, Step -> Leaper)]
--     unending = for ls \case
--       End -> Nothing
--       Continue k f -> Just (k, f)

--     go :: RingView (Int, Step -> Leaper) -> Leaper
--     go r =
--       let lo = r ^. mini . _1
--           hi = r ^. maxi . _1
--           alt f = go $ rotateRingL $ r & mini .~ f
--        in if lo == hi
--             then Continue lo \step -> case (r ^. mini . _2) step of
--               End -> End
--               Continue n f -> alt (n, f)
--             else case (r ^. mini . _2) (Leap hi) of
--               End -> End
--               Continue n f -> alt (n, f)

-- data Shaped f a = Shaped (f a) a
--   deriving (Functor, Foldable, Traversable)

-- queryByShape :: forall f. Language f => f () -> BG f Leaper
-- queryByShape f = do
--   m <- submapBetween (f $> Id minBound, f $> Id maxBound) <$> use share
--   pure (go 0 m)
--   where
--     go :: Int -> Map (f Id) Id -> Leaper
--     go depth m = case Map.minViewWithKey m of
--       Nothing -> End
--       Just ((f'', i''), m') ->
--         let s = Shaped f'' i''
--          in case s ^? elementOf traverse depth of
--               Nothing -> End
--               Just i' ->
--                 Continue
--                   (_unId i')
--                   ( \case
--                       Next -> go depth m'
--                       Leap n ->
--                         let Shaped f' _i = s & elementOf traverse depth .~ Id n
--                          in go depth (dropWhileAntitone (< f') m')
--                       StepIn -> go (depth + 1) m'
--                       StepOut -> go (depth - 1) m'
--                   )

-- triejoin :: [Leaper] -> Leaper
-- triejoin = _

{-
  given
  R :: Leaper
  S :: Leaper
  T :: Leaper
  we want to do

  leapfrog [R, T] -> Q
  leapFrog Q
-}

-- data Foo a
--   = H a a
--   | G Int
--   deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

-- instance Hashable a => Hashable (Foo a)

-- instance Language Foo

-- instance Show1 Foo where
--   liftShowsPrec sp sl p (H a b) = showsBinaryWith sp sp "F" p a b
--   liftShowsPrec sp sl p (G i) = showsUnaryWith showsPrec "G" p i

-- test :: String
-- test = show $
--   evaluatingState emptyBee $ do
--     g0 <- insertBee (G 0)
--     g1 <- insertBee (G 1)
--     g2 <- insertBee (G 2)
--     g3 <- insertBee (G 3)
--     unionBee g1 g2
--     f1 <- insertBee (H g0 g1)
--     f2 <- insertBee (H f1 g1)
--     f3 <- insertBee (H f2 g1)
--     f4 <- insertBee (H f3 g1)
--     unionBee f4 g3
--     rebuild
--     l <- queryByShape (H () ())
--     pure (takeTheL 10 l)