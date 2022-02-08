{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

module Beegraph where

import Control.Lens
import Data.Functor.Reverse (Reverse (Reverse))
import Data.HashMap.Strict qualified as HashMap
import Data.IntMap.Strict qualified as IntMap
import Data.Traversable (for)

class (Traversable f, Eq (f Id), Hashable (f Id), Eq (f ()), Hashable (f ())) => Language f

type Id = Int

{-
  we have two kinds of node:
  unsaturated nodes: have map (arg: Id) → more saturated parent
  saturated nodes: have a rank and a parent
-}

type Unsaturated = IntMap Id

data Saturated f = Saturated
  { _parent :: Id,
    _rank :: Word32,
    _sat :: f Id
  }

makeLenses ''Saturated

data Beegraph f = Beegraph
  { _nodes :: IntMap (Either Unsaturated (Saturated f)),
    _unsat :: HashMap (f ()) Id,
    _next :: Id
  }

makeLenses ''Beegraph

nextId :: State (Beegraph f) Id
nextId = do
  newNode <- use next
  next += 1
  pure newNode

union :: Language f => Id -> Id -> State (Beegraph f) ()
union x y = do
  x' <- find' x
  y' <- find' y
  when (x /= y) $ do
    _

insert :: Language f => f Id -> State (Beegraph f) Id
insert node = do
  root <- use (unsat . at (void node))
  root' <- maybe (nextId >>= \i -> unsat . at (void node) .= Just i >> pure i) pure root
  node' <- traverse find' node
  foldr _ (pure root') u node'
  _

-- use (unsat . at (void node)) >>= \case
--   Just id -> do
--     node' <- traverse find' node
--     foldr
--       ( \current prev -> do
--           pred <- prev
--           y <- preuse $ nodes . ix pred . _Left . ix current
--           _
--       )
--       (pure id)
--       node'
--   Nothing -> do
--     node' <- traverse find' node
--     newNode <- nextId
--     last <-
--       foldr
--         ( \current prev -> do
--             parent <- prev
--             newNode <- nextId
--             nodes . at newNode .= Just (Left $ IntMap.insert current parent mempty)
--             pure current
--         )
--         (pure newNode)
--         (Reversed node')
--     nodes . at newNode .= Just (Right $ Saturated newNode 0 node)
--     unsat . at (void node) .= Just last
--     pure newNode

find' :: Language f => Id -> State (Beegraph f) Id
find' id = state $ \graph -> case IntMap.lookup id (_nodes graph) of
  Nothing -> (id, graph)
  Just (Left _us) -> (id, graph)
  Just (Right s) -> go (void (_sat s)) (toList (_sat s))
  where
    go :: f () -> [Id] -> (Id, Beegraph f)
    go _ [] = _
