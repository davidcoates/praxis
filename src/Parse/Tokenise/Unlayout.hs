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
unlayout wrapInBlock tokens = if wrapInBlock then [lbrace] ++ tokens' ++ [rbrace] else tokens' where tokens' = unlayout' [] (lines tokens)

lines :: [Sourced Token] -> [[Sourced Token]]
lines []     = []
lines (x:xs) = case lines xs of
  []   -> [[x]]
  l:ls -> if (line . start . view tag) (head l) == (line . end . view tag) x then (x:l):ls else [x] : l : ls

unlayout' :: [Int] -> [[Sourced Token]] -> [Sourced Token]
unlayout' [] []     = []
unlayout' is []     = replicate (length is - 1) rbrace
unlayout' is (l:ls) = let li = (column . start . view tag) (head l) in case is of
  [] -> l ++ unlayout' [li] ls
  _  -> case compare li (head is) of
    GT -> (lbrace : l) ++ unlayout' (li : is) ls
    EQ -> (semi : l) ++ unlayout' is ls
    LT -> rbrace : unlayout' (tail is) (l : ls)
