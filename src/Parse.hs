{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Parse
  ( Parseable(..)
  ) where

import           AST
import           Parse.Desugar  (Desugarable (..))
import qualified Parse.Parse    as Sweet (Parseable (..))
import           Parse.Tokenise (tokenise)
import           Praxis
import           Source         (Source)
import           Tag
import           Type           (Impure)

type Annotated a = Tagged Source a

class Parseable a where
  parse  :: String -> Praxis (Annotated a)

parse' :: (Sweet.Parseable (Sweet a), Desugarable a) => Bool -> String -> Praxis (Annotated a)
parse' b s = do
  ts <- tokenise b s
  p <- Sweet.parse ts
  desugar p

instance Parseable Program where
  parse = parse' True

instance Parseable Exp where
  parse = parse' False

instance Parseable (Lift Impure) where
  parse = parse' False
