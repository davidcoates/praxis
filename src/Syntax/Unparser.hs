{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Syntax.Unparser
  ( Unparser(..)
  ) where

import           Common
import           Introspect    (Complete)
import           Syntax.Prism
import           Syntax.Syntax (Domain, Syntax)
import qualified Syntax.Syntax
import           Token

class Unparser f where
  (>$<) :: (b -> Maybe a) -> f a -> f b
  (>*<) :: f a -> f b -> f (a, b)
  empty :: f a
  token :: f Token
  annotated :: Complete s => f (a s) -> f (Annotated s a)

instance Unparser f => Syntax f where
  f <$> p = destruct f >$< p
  (<*>) = (>*<)
  empty = empty
  p <|> q = (\x -> Just (x, x)) >$< (p >*< q)
  pure = const empty
  match _ f = (Just . f) >$< token
  mark = const empty
  unparseable = id

instance (Unparser f, Complete s) => Domain f s where
  annotated = annotated
  combine = error "<unparser combine>"
