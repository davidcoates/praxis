{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Syntax.Unparser
  ( Unparser(..)
  , unparse
  ) where

import           Common
import           Introspect
import           Syntax.AST
import           Syntax.Prism
import           Syntax.Syntax (Domain, Syntax)
import qualified Syntax.Syntax as Syntax
import qualified Syntax.Syntax
import           Token

class Unparser f where
  (>$<) :: (b -> Maybe a) -> f a -> f b
  (>*<) :: f a -> f b -> f (a, b)
  empty :: f a
  (<|>) :: f a -> f a -> f a
  token :: f Token
  annotated :: Complete s => f (a s) -> f (Annotated s a)
  mark :: String -> f a

-- Wrap to avoid overlapping Syntax and Domain instances
newtype T f a = T { unT :: f a }

instance Unparser f => Syntax (T f) where
  f <$> T p = T $ destruct f >$< p
  T p <*> T q = T (p >*< q)
  empty = T empty
  T p <|> T q = T (p <|> q)
  pure = const (T empty)
  match _ f = T $ (Just . f) >$< token
  mark = T . mark
  unparseable = id

instance (Unparser f, Complete s) => Domain (T f) s where
  annotated (T p) = T (annotated p)
  combine = error "<unparser combine>"

unparse :: forall a f s. (Recursive a, Unparser f, Complete s) => f (Annotated s a)
unparse = unT (Syntax.annotated (syntax (witness :: I a)))

