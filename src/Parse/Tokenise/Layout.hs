module Parse.Tokenise.Layout
  ( layout
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

layout :: Bool -> [Sourced Token] -> [Sourced Token]
layout block ts = if block then [lbrace] ++ ts' ++ [rbrace] else ts' where ts' = layout' [] (lines ts)

lines :: [Sourced Token] -> [[Sourced Token]]
lines []     = []
lines (x:xs) = case lines xs of
    []   -> [[x]]
    l:ls -> if (line . start . view tag) (head l) == (line . end . view tag) x then (x:l):ls else [x] : l : ls

layout' :: [Int] -> [[Sourced Token]] -> [Sourced Token]
layout' [] []     = []
layout' is []     = replicate (length is - 1) rbrace
layout' is (l:ls) = let li = (column . start . view tag) (head l) in case is of
    [] -> l ++ layout' [li] ls
    _  -> case compare li (head is) of
        GT -> (lbrace : l) ++ layout' (li : is) ls
        EQ -> (semi : l) ++ layout' is ls
        LT -> rbrace : layout' (tail is) (l : ls)
