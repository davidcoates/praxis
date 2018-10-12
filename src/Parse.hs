{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Parse
  ( Parseable(..)
  , Parsed(..)
  ) where

import           AST
import           Common
import           Parse.Annotate
import           Parse.Desugar   (Desugarable (..))
import qualified Parse.Parse     as Sweet (Parseable (..))
import qualified Parse.Parse.AST as Sweet (Exp, Program)
import           Parse.Tokenise  (tokenise)
import           Praxis
import           Source          (Source)
import           Tag
import           Type            (Kind, Type)

class Parseable a where
  parse  :: String -> Praxis (Parsed a)

instance Parseable Program where
  parse s = do
    ts <- tokenise True s
    p <- Sweet.parse ts :: Praxis (Parsed Sweet.Program)
    desugar p

instance Parseable Exp where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Parsed Sweet.Exp)
    desugar p

instance Parseable Type where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Parsed Type)
    desugar p

instance Parseable (Const Kind) where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Parsed (Const Kind))
    desugar p
