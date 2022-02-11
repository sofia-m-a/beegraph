{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
-- needed for some 'Show' instances...
{-# LANGUAGE UndecidableInstances #-}

module Beegraph where

import Control.Comonad (extract)
import Control.Comonad.Cofree
import Control.Lens hiding ((:<))
import Control.Monad.Trans.Accum
import Data.Foldable (maximum)
import Data.These (These (That, These, This))
import Data.Traversable (for)
import Data.Zip (Semialign (align))
import Witherable
import Prelude hiding (mapMaybe)

class (Traversable f, Eq (f ()), Hashable (f ())) => Language f

type Id = Int

data Node f = Node
  { -- map from argument to a parent node that's this node applied to that argument
    _parents :: IntMap Id,
    -- a node equal to this (like an 'epsilon' argument parent)
    _parent :: Id,
    -- depth of epsilon-children of this node
    _rank :: Int32,
    -- how we made this node
    _root :: f (),
    _path :: [Id],
    -- if this node is saturated (an output node)
    _sat :: Maybe (f Id)
  }

deriving instance (Show (f ()), Show (f Id)) => Show (Node f)

makeLenses ''Node

data Beegraph f = Beegraph
  { -- map from id to node
    _nodes :: IntMap (Node f),
    -- map from root constructor to id
    _roots :: HashMap (f ()) Id,
    -- the next 'Id' to use
    _next :: Id
  }

makeLenses ''Beegraph

deriving instance (Show (f ()), Show (f Id)) => Show (Beegraph f)

type BG f a = State (Beegraph f) a

withNextId :: (Id -> BG f ()) -> BG f Id
withNextId f = do
  i <- use next
  next += 1
  f i
  pure i

withNode :: Id -> (Node f -> BG f Id) -> BG f Id
withNode i f = do
  n <- preuse (nodes . ix i)
  maybe (pure i) f n

-- | merges two maps, 'unionBee'ing any common 'Id's
merge :: Language f => IntMap Id -> IntMap Id -> BG f (IntMap Id)
merge a b = for (align a b) $
  \case
    This a' -> pure a'
    That b' -> pure b'
    These a' b' -> do
      a' `unionBee` b'
      pure b'

-- | looks for a parent node for current, using a stack of transitions to make, and a map of
seek :: Language f => Id -> [Id] -> IntMap Id -> BG f Id
seek current stack drag = do
  withNode current $ \n' -> do
    let epsilon = _parent n'
    let rest = _parents n'
    -- if this node has an equivalent parent
    if epsilon /= current
      then do
        -- detach the nodes we're about to drag away
        nodes . ix current . parents .= mempty
        -- optimize the path
        grandparent <- preuse (nodes . ix epsilon . parent)
        for_ grandparent (\gp -> nodes . ix current . parent .= gp)
        -- continue dragging behind our other parents
        seek epsilon stack =<< drag `merge` rest
      else case stack of
        [] -> pure current
        (s : ss) -> do
          s' <- findBee s
          let c = rest ^? ix s
          let c' = rest ^? ix s'
          s'' <- case (c, c') of
            (Nothing, Nothing) -> withNextId $ \g -> do
              nodes . at g .= Just (Node mempty g 0 (_root n') (_path n' ++ [s']) Nothing)
              nodes . ix current . parents . at s' .= Just g
            (Just k, Nothing) -> do
              nodes . ix current . parents . at s' .= Just k
              pure k
            (_, Just k') -> pure k'
          seek s'' ss drag

findBee :: Language f => Id -> BG f Id
findBee i = do
  withNode i $ \n -> do
    root' <- preuse (roots . ix (n ^. root))
    maybe (pure i) (\root'' -> seek root'' (n ^. path) mempty) root'

unionBee :: Language f => Id -> Id -> BG f ()
unionBee a' b' = do
  a <- findBee a'
  b <- findBee b'
  an' <- preuse (nodes . ix a)
  bn' <- preuse (nodes . ix b)
  when (a /= b) $
    whenJust (liftA2 (,) an' bn') $ \(an, bn) -> do
      let (larger, smaller) = if an ^. rank > bn ^. rank then (a, b) else (b, a)
      nodes . ix smaller . parent .= larger
      when (an ^. rank == bn ^. rank) $
        nodes . ix larger . rank += 1

insertBee :: Language f => f Id -> BG f Id
insertBee f = do
  -- try to find an existing root
  r <- preuse (roots . ix (void f))
  -- otherwise, create a new root
  r' <-
    whenNothing
      r
      ( withNextId $ \next' -> do
          roots . at (void f) .= Just next'
          nodes . at next' .= Just (Node mempty next' 0 (void f) [] Nothing)
      )
  -- and find our way to the top
  top <- seek r' (toList f) mempty
  -- make sure we mark the top node as saturated
  nodes . ix top . sat %= \s -> s <|> Just f
  pure top

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

extractBee :: forall f a. (Language f, Ord a) => (f a -> a) -> BG f (IntMap (Weighted f a))
extractBee weigh = do
  -- normalize all nodes
  get >>= (nodes . traversed . sat . _Just . traversed $ findBee)
  graph <- get
  -- extract saturated nodes
  let tops = mapMaybe (\n' -> (\sat' -> Extractor sat' (_parent n') Nothing) <$> _sat n') (graph ^. nodes)
  -- find the fixpoint
  let f = executingState tops $ fixpoint (const propagate) ()
  -- extract minimum trees
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
      ifor_
        map'
        ( \index' node -> do
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
        )
