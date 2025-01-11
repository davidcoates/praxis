{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

module Syntax.Unparser
  ( Unparser(..)
  , unparse
  ) where

import           Common
import           Introspect
import           Stage
import           Syntax.Prism
import qualified Syntax.Syntax
import qualified Syntax.Syntax as Syntax
import           Syntax.Syntax (Syntax)
import           Syntax.Term
import           Term
import           Token

class Unparser f where
  (>$<) :: (b -> Maybe a) -> f a -> f b
  (>*<) :: f a -> f b -> f (a, b)
  empty :: f a
  (<|>) :: f a -> f a -> f a
  token :: f Token
  annotated :: (IsTerm a, IsStage s) => f (a s) -> f (Annotated s a)
  expected :: String -> f a

newtype T f a = T { unT :: f a }

instance Unparser f => Syntax (T f) where
  f <$> T p = T $ destruct f >$< p
  T p <*> T q = T (p >*< q)
  empty = T empty
  T p <|> T q = T (p <|> q)
  pure = const (T empty)
  match _ f = T $ (Just . f) >$< token
  expected = T . expected
  internal = id
  annotated (T p) = T (annotated p)

unparse :: forall f a s. (Unparser f, IsTerm a, IsStage s) => f (Annotated s a)
unparse = unT (Syntax.annotated (syntax (termT :: TermT a)))
