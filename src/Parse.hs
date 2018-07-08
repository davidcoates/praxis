{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Parse
  ( Parseable(..)
  , Annotated(..)
  ) where

import           AST
import           Parse.Desugar   (Desugarable (..))
import qualified Parse.Parse     as Sweet (Parseable (..))
import qualified Parse.Parse.AST as Sweet (Exp, Program)
import           Parse.Tokenise  (tokenise)
import           Praxis
import           Source          (Source)
import           Tag
import           Type            (Kind, Kinded, Type)

type Annotated a = Tagged Source a

class Parseable a where
  parse  :: String -> Praxis a

instance Parseable (Annotated Program) where
  parse s = do
    ts <- tokenise True s
    p <- Sweet.parse ts :: Praxis (Annotated Sweet.Program)
    desugar p

instance Parseable (Annotated Exp) where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Annotated Sweet.Exp)
    desugar p

instance Parseable (Annotated Type) where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis (Annotated Type)
    desugar p

instance Parseable Kind where
  parse s = do
    ts <- tokenise False s
    p <- Sweet.parse ts :: Praxis Kind
    desugar p
