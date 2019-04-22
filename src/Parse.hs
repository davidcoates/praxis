{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Parse
  ( Parseable(..)
  , Parsed(..)
  ) where

import           Annotate
import           AST
import           Common
import           Kind           (Kind)
import           Parse.Desugar  (Desugarable (..))
import qualified Parse.Parse    as Sweet
import           Parse.Tokenise (tokenise)
import           Praxis
import           Type           (Type)

class Parseable a where
  parse  :: String -> Praxis (Parsed a)

instance Parseable Program where
  parse s = do
    ts <- tokenise True s
    p <- Sweet.parse ts :: Praxis (Parsed Program)
    desugar p

instance Parseable Exp where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Parsed Exp)
    desugar p

instance Parseable Type where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Parsed Type)
    desugar p

instance Parseable Kind where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Parsed Kind)
    desugar p
