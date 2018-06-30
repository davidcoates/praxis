{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Parse
  ( parse
  , parseFree
  ) where

import           Compiler
import           Parse.Desugar  (Desugarable, desugar, desugarFree)
import qualified Parse.Parse    as Sweet (Parseable, parse, parseFree)
import           Parse.Tokenise (tokenise)
import           Source         (Source)
import           Tag            (Tag)

parse :: Compiler ()
parse =  tokenise >> Sweet.parse >> desugar

-- Currently, b can be one of:
--  * Annotated Program
--  * Tag Source Type
--  (where Annotated means Parse.Desugar.Annotated)
parseFree :: (Sweet.Parseable a, Desugarable (Tag Source a) b) => Compiler b
parseFree = do
  x <- Sweet.parseFree
  desugarFree x
