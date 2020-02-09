{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Syntax.Unparser
  ( Unparser(..)
  , unparse
  ) where

import           Common
import           Introspect
import           Syntax.Prism
import           Syntax.Syntax (Syntax)
import qualified Syntax.Syntax as Syntax
import qualified Syntax.Syntax
import           Syntax.Term
import           Term
import           Token

class Unparser f where
  (>$<) :: (b -> Maybe a) -> f a -> f b
  (>*<) :: f a -> f b -> f (a, b)
  empty :: f a
  (<|>) :: f a -> f a -> f a
  token :: f Token
  annotated :: Recursive a => f a -> f (Annotated a)
  mark :: String -> f a

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
  annotated (T p) = T (annotated p)
  combine = error "<unparser combine>"

unparse :: forall a f. (Recursive a, Unparser f) => f (Annotated a)
unparse = unT (Syntax.annotated (syntax (witness :: I a)))

