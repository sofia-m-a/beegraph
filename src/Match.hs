{-# LANGUAGE TemplateHaskell #-}

module Match where

import Beegraph
import Control.Comonad.Cofree (_extract)
import Control.Lens

type Sub f = IntMap (TermTree f)

newtype TermTree f = TermTree {_termTree :: f (Either Id (TermTree f))}

makeLenses ''TermTree

run :: forall f a. (Ord a, Language f) => (f a -> a) -> Beegraph f (Maybe (Sub f)) -> IntMap (Weighted f a)
run weigh graph = evaluatingState graph go
  where
    runTree :: forall i. TermTree f -> BG f i Id
    runTree (TermTree f) = traverse (traverse runTree) f >>= insertBee . fmap (either id id)

    go :: BG f (Maybe (Sub f)) (IntMap (Weighted f a))
    go = do
      sub <- use (watcher . _extract)
      case sub of
        Nothing -> extractBee weigh
        Just im -> do
          ifor_ im \i term -> do
            j <- runTree term
            i `unionBeeId` j
            pure ()
          go
