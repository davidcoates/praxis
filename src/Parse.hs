{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Parse
  ( parse
  , parseFree
  ) where

import           Parse.Desugar  (Desugarable, desugar, desugarFree)
import qualified Parse.Parse    as Sweet (Parseable, parse, parseFree)
import           Parse.Tokenise (tokenise)
import           Praxis
import           Source         (Source)
import           Tag            (Tag)

parse :: Praxis ()
parse =  tokenise >> Sweet.parse >> desugar

-- Currently, b can be one of:
--  * Annotated Program
--  * Annotated Exp
--  * Tag Source Type
--  (where Annotated means Parse.Desugar.Annotated)
parseFree :: (Sweet.Parseable a, Desugarable (Tag Source a) b) => String -> Praxis b
parseFree s = do
  set src s
  tokenise
  x <- Sweet.parseFree
  desugarFree x
