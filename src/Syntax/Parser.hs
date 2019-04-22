{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Syntax.Parser
  ( Parser(..)
  ) where

import           Annotate
import           Common
import           Syntax.Prism
import           Syntax.Syntax       (Domain, Syntax)
import qualified Syntax.Syntax
import           Token

import           Control.Applicative (Alternative (..))
import           Data.Maybe          (fromJust, isJust)

class Alternative f => Parser f where
  match :: (Token -> Bool) -> f Token
  mark :: String -> f a
  sourced :: f a -> f (Sourced a)

instance Parser f => Syntax f where
  f <$> p = construct f <$> p
  p <*> q = (,) <$> p <*> q
  empty = empty
  (<|>) = (<|>)
  pure = pure
  match f _ = fromJust . f <$> match (isJust . f)
  mark = mark
  unparseable = const empty

instance Parser f => Domain f Parse where
  annotated p = (\(s :< p) -> (s, ()) :< p) <$> sourced p
  combine _ f (p, q) = (view source p <> view source q, ()) :< f (p, q)
