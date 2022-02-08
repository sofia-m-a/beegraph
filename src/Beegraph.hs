{-# LANGUAGE ImportQualifiedPost #-}

module Beegraph where

import Data.Array.ST.Safe
import Data.HashMap.Strict qualified as HashMap

class (Traversable f, Eq (f Id), Hashable (f Id)) => Language f

type Id = Int

{-
  we have two kinds of node:
  unsaturated nodes: have map (arg: Id) → more saturated parent
  saturated nodes: have a rank and a parent
-}

type Unsaturated = IntMap Id

data Saturated = Saturated
  { parent :: Id,
    rank :: Word32
  }

data Beegraph f = Beegraph
  { nodes :: IntMap (Either Unsaturated Saturated),
    share :: HashMap (f Id) Id
  }

union :: Language f => Id -> Id -> Beegraph f -> Beegraph f
union = _

insert :: Language f => f Id -> Beegraph f -> Beegraph f
insert = _

find :: Language f => Beegraph f -> Id -> Id
find = _

-- find :: Language f => Beegraph f -> f Id -> f Id
-- find bee f = go (void f) (toList f)
--   where
--     go node [] = case HashMap.lookup _ (graph bee) of

-- import Control.Monad.ST.Trans (STRef, STT, newSTRef, readSTRef, writeSTRef)
-- import Data.Equivalence.STT
-- import Data.HashMap.Strict qualified as HashMap
-- union :: Node -> Node -> Beegraph -> Beegraph

-- find :: Beegraph -> Node -> Node

{-
    f   a
    f   b
    a ~ b
    g x y ~ f b
    h x ~ g x z
    y ~ z

    find f a, h x should be the same.
       find f a
    => find f a [find a]
    => find f a [b]
    => find f b

       find h x
    => find h x [find x]
    => find h x [x]
    => find h x
    => find g x z [find x]
    => find g x ????

    find [g x z]
    => find [g] x z
    => find [g x] z
    => find [y~z/g x z, z~z/g x z]
-}

-- data EClass f = EClass
--   { id :: Id,
--     nodes :: Seq (f Id),
--     parents :: Seq (f Id, Id)
--   }

-- data EGraph s f = EGraph
--   { equiv :: Equiv s Id Id, -- Id ~ Id
--     eclass :: STRef s (IntMap (EClass f)), -- Id → EClass
--     share :: STRef s (HashMap (f Id) Id), -- f Id ~ Id
--     worklist :: STRef s (Seq Id), -- Ids to upward-merge
--     next :: STRef s Id
--   }

-- type EM s a = STT s Identity a

-- add :: Language f => f Id -> EGraph s f -> EM s Id
-- add enode graph = do
--   enode' <- canonicalize graph enode
--   share' <- readSTRef (share graph)
--   whenNothing (HashMap.lookup enode' share') $ do
--     eclassId <- readSTRef (next graph)
--     writeSTRef (next graph) (eclassId + 1)
--     traverse
--       ( \child -> do
--           eclass' <- readSTRef (eclass graph)

--       )
--       enode'
--     writeSTRef (share graph) (HashMap.insert enode' eclassId share')
--     pure eclassId

-- merge :: Id -> Id -> EGraph s f -> EM s Id
-- merge a b graph = do
--   eq <- liftA2 (==) (efind graph a) (efind graph b)
--   if eq
--     then efind graph a
--     else do
--       equate (equiv graph) a b
--       newId <- efind graph a
--       wl <- readSTRef (worklist graph)
--       writeSTRef (worklist graph) (one newId <> wl)
--       pure newId

-- canonicalize :: Language f => EGraph s f -> f Id -> EM s (f Id)
-- canonicalize = traverse . efind

-- efind :: EGraph s f -> Id -> EM s Id
-- efind graph id = do
--   c <- getClass (equiv graph) id
--   desc (equiv graph) c
