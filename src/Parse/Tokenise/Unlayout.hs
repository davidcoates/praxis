module Parse.Tokenise.Unlayout
  ( unlayout
  ) where

import           Common
import           Prelude hiding (lines)
import           Token

lbrace :: Sourced Token
lbrace = Phantom :< Layout '{'

rbrace :: Sourced Token
rbrace = Phantom :< Layout '}'

semi :: Sourced Token
semi = Phantom :< Layout ';'

unlayout :: Bool -> [Sourced Token] -> [Sourced Token]
unlayout wrapInBlock tokens = unlayout' (if wrapInBlock then [-1] else []) (lines tokens)

lines :: [Sourced Token] -> [[Sourced Token]]
lines []     = []
lines (x:xs) = case lines xs of
  []   -> [[x]]
  l:ls -> if (line . start . view tag) (head l) == (line . end . view tag) x then (x:l):ls else [x] : l : ls

unlayout' :: [Int] -> [[Sourced Token]] -> [Sourced Token]
unlayout' [] []     = []
unlayout' is []     = replicate (length is - 1) rbrace
unlayout' is (l:ls) = case is of
    [] -> l ++ unlayout' [li] ls
    _  -> case compare li (head is) of
      GT -> (layout '{' : l) ++ unlayout' (li : is) ls
      EQ -> (layout ';' : l) ++ unlayout' is ls
      LT -> (layout '}') : unlayout' (tail is) (l : ls)
  where
    src = view tag (head l)
    li = (column . start) src
    layout :: Char -> Sourced Token
    layout c = Source { start = start src, end = start src } :< Layout c
