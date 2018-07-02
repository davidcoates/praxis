module Parse.Tokenise.Layout
  ( layout
  ) where

import           Parse.Tokenise.Token
import           Praxis
import           Source
import           Tag

lbrace :: Annotated Token
lbrace = Phantom :< Special '{'

rbrace :: Annotated Token
rbrace = Phantom :< Special '}'

semi :: Annotated Token
semi = Phantom :< Special ';'

-- |Inserts phantom layout tokens based on indentation
layout :: [Annotated Token] -> Praxis [Annotated Token]
layout ts = do
  s <- get (flags . static) -- TODO make this more robust
  return $ l (-1) (not s) [] ts
  where l :: Int -> Bool -> [Int] -> [Annotated Token] -> [Annotated Token] -- This function works by magic
        l i b cs (t@(_:<Whitespace):ts) = t : l i b cs ts
        l i b cs [] = replicate (length cs) rbrace
        l i True cs (t@(_:<Special '{'):ts) = t : l i False cs ts
        l i b cs (t@(a:<x):ts) | b         = lbrace : t : l i' b' (j:cs) ts
                               | null cs   = t : l i' b' cs ts
                               | i' > i    = case compare j (head cs) of LT -> rbrace : l i b (tail cs) (t:ts)
                                                                         EQ -> semi : t : l i' b' cs ts
                                                                         GT -> t : l i' b' cs ts
                               | otherwise = t : l i' b' cs ts
          where i' = line . end $ a
                j  = column . start $ a
                b' = case x of ReservedId x -> x `elem` ["do", "of", "where"]
                               _            -> False

