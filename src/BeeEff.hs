module BeeEff where

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
parse s = reverse <$> go [] [] s
  where
    go is [] "" = Just is
    go _ _ "" = Nothing -- unmatched left bracket
    go is ks (s : ss) | Just i <- single s = go (i : is) ks ss
    go is ks ('[' : ss) = go [] (is : ks) ss
    go is (js : ks) (']' : ss) = go (Loop is : js) ks ss
    go _ [] (']' : _) = Nothing -- unmatched right bracket
    go is ks (_ : ss) = go is ks ss

rle :: [Instruction] -> [Instruction]
rle (Add n : Add m : xs) = rle (Add (n + m) : xs)
rle (Move n : Move m : xs) = rle (Move (n + m) : xs)
rle (Loop is : xs) = Loop (rle is) : rle xs
rle (x : xs) = x : rle xs
rle [] = []