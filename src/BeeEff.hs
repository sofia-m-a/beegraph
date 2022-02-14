module BeeEff where

import Beegraph (BG, Id, Language, emptyBee, insertBee, unionBee)
import Control.Comonad.Cofree (Cofree, coiter)
import Control.Comonad.Trans.Cofree (CofreeF ((:<)))
import Control.Lens hiding ((:<))
import Data.Functor.Foldable (cata)
import qualified Data.IntMap as IntMap
import Match
import Prettyprinter

data Instruction
  = Add Int
  | Move Int
  | In
  | Out
  | Loop [Instruction]
  deriving (Show)

single :: Char -> Maybe Instruction
single = \case
  '+' -> Just $ Add 1
  '-' -> Just $ Add (-1)
  '<' -> Just $ Move (-1)
  '>' -> Just $ Move 1
  ',' -> Just In
  '.' -> Just Out
  _ -> Nothing

parse :: String -> Maybe [Instruction]
parse = go [] []
  where
    --    instructions     blocks to process  input
    go :: [Instruction] -> [[Instruction]] -> String -> Maybe [Instruction]
    -- nothing left to process
    go is [] "" = Just is
    -- unmatched left bracket
    go _ (_ : _) "" = Nothing
    -- process single instruction
    go is ks (s' : ss) | Just i <- single s' = go (i : is) ks ss
    -- begin block
    go is ks ('[' : ss) = go [] (is : ks) ss
    -- end block
    go is (js : ks) (']' : ss) = go (Loop is : js) ks ss
    -- unmatched right bracket
    go _ [] (']' : _) = Nothing
    -- comment
    go is ks (_ : ss) = go is ks ss

rle :: [Instruction] -> [Instruction]
rle (Add n : Add m : xs) = rle (Add (n + m) : xs)
rle (Move n : Move m : xs) = rle (Move (n + m) : xs)
rle (Loop is : xs) = Loop (rle is) : rle xs
rle (x : xs) = x : rle xs
rle [] = []

data Pyro a
  = PyAdd a a
  | PyInt Int
  | PyPi1 a
  | PyPi2 a
  | PyPair a a
  | PyLoad a a
  | PyStore a a a
  | PyIn a
  | PyOut a a
  | PyEq a a
  | PyStartIO
  | PyZeroArray
  | PyEndIo a
  | PyIf a a a
  | PyStream a a
  | PyFindFirst a
  | PySelect a a
  | PyFake Word
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Pyro a)

instance Language Pyro

instance (Show a, Pretty a) => Pretty (Pyro a) where
  pretty = \case
    PyAdd a a' -> "add" <+> pretty a <+> pretty a'
    PyInt n -> pretty n
    PyPi1 a -> "π₁" <+> pretty a
    PyPi2 a -> "π₂" <+> pretty a
    PyPair a a' -> parens (pretty a <> comma <+> pretty a')
    PyLoad a a' -> "load from:" <+> pretty a <+> "at:" <+> pretty a'
    PyStore a a' a3 -> "store to:" <+> pretty a <+> "at:" <+> pretty a' <+> pretty a3
    PyIn a -> "in" <+> pretty a
    PyOut a a' -> "out" <+> pretty a <+> pretty a'
    PyEq a a' -> "eq" <+> pretty a <+> pretty a'
    PyStartIO -> "start-io"
    PyZeroArray -> "zero-array"
    PyEndIo a -> "end-io" <+> pretty a
    PyIf a a' a3 -> "if" <+> pretty a <+> "then" <+> pretty a' <+> "else" <+> pretty a3
    PyStream a a' -> "stream start:" <+> pretty a <+> pretty a'
    PyFindFirst a -> "find-first" <+> pretty a
    PySelect a a' -> "select from:" <+> pretty a <+> "at:" <+> pretty a'
    PyFake _wo -> "FAKE"

-- utterly disgusting
build :: [Instruction] -> BG Pyro Id
build is = do
  io <- insertBee PyStartIO
  mem <- insertBee PyZeroArray
  tape <- insertBee $ PyInt 0
  view _1 <$> foldr go (pure (io, mem, tape, 0)) is
  where
    go :: Instruction -> BG Pyro (Id, Id, Id, Word) -> BG Pyro (Id, Id, Id, Word)
    go i imt = do
      (io, mem, tape, fake) <- imt
      case i of
        Add n -> do
          lit <- insertBee $ PyInt n
          l <- insertBee $ PyLoad mem tape
          r <- insertBee $ PyAdd l lit
          mem' <- insertBee $ PyStore mem tape r
          pure (io, mem', tape, fake)
        Move n -> do
          lit <- insertBee $ PyInt n
          tape' <- insertBee $ PyAdd tape lit
          pure (io, mem, tape', fake)
        In -> do
          v <- insertBee $ PyIn io
          io' <- insertBee $ PyPi1 v
          r <- insertBee $ PyPi2 v
          mem' <- insertBee $ PyStore mem tape r
          pure (io', mem', tape, fake)
        Out -> do
          r <- insertBee $ PyLoad mem tape
          io' <- insertBee $ PyOut io r
          pure (io', mem, tape, fake)
        -- I warned you:
        Loop ins -> do
          loopIOf <- insertBee $ PyFake $ fake + 0
          loopMemf <- insertBee $ PyFake $ fake + 1
          loopTapef <- insertBee $ PyFake $ fake + 2
          (lbi, lbm, lbt, fake') <- foldr go (pure (io, mem, tape, fake + 3)) ins
          loopIO <- insertBee $ PyStream io lbi
          unionBee loopIO loopIOf
          loopMem <- insertBee $ PyStream mem lbm
          unionBee loopMem loopMemf
          loopTape <- insertBee $ PyStream tape lbt
          unionBee loopTape loopTapef
          v0 <- insertBee $ PyInt 0
          vl <- insertBee $ PyLoad loopMem loopTape
          cond <- insertBee $ PyEq v0 vl
          head' <- insertBee $ PyFindFirst cond
          headIO <- insertBee $ PySelect loopIO head'
          headMem <- insertBee $ PySelect loopMem head'
          headTape <- insertBee $ PySelect loopTape head'
          pure (headIO, headMem, headTape, fake')

-- simple attempt at giving costs to pyro instructions
weighPyro :: Pyro Word -> Word
weighPyro = \case
  PyAdd wo wo' -> 1 + wo + wo'
  PyInt _ -> 1
  PyPi1 wo -> 1 + wo
  PyPi2 wo -> 1 + wo
  PyPair wo wo' -> 1 + wo + wo'
  PyLoad wo wo' -> 4 + wo + wo'
  PyStore wo wo' wo2 -> 4 + wo + wo' + wo2
  PyIn wo -> 1 + wo
  PyOut wo wo' -> 1 + wo + wo'
  PyEq wo wo' -> 1 + wo + wo'
  PyStartIO -> 0
  PyZeroArray -> 0
  PyEndIo wo -> 0 + wo
  PyIf wo wo' wo2 -> 1 + wo + wo' `max` wo2
  PyStream wo wo' -> 1 + wo + 10 * wo'
  PyFindFirst wo -> 1 + wo
  PySelect wo wo' -> 1 + wo + wo'
  PyFake _wo -> 0

-- analyze :: String -> Maybe (Cofree Pyro Word)
-- analyze =
--   parse
--     >=> rle
--     >>> build
--     >>> usingState emptyBee
--     >>> second (run weighPyro)
--     >>> uncurry IntMap.lookup
--     >=> evaluatingState (0 :: Word)
--       . traverse
--         ( \_weight -> do
--             s <- get
--             put (s + 1)
--             pure s
--         )
--     >>> pure

prettyPyro :: Cofree Pyro Word -> Doc ann
prettyPyro = snd . prettyPyro'
  where
    prettyPyro' :: Cofree Pyro Word -> (Word, Doc ann)
    prettyPyro' = cata \(name :< body) ->
      ( name,
        vsep (toList $ fmap snd body)
          <> ( if null (toList body)
                 then mempty
                 else line
             )
          <> pretty name <+> "←" <+> pretty (fmap fst body)
          -- <> line
      )