{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Syntax.Parser
  ( Parser(..)
  , parse
  ) where

import           Common
import           Introspect
import           Syntax.Prism
import           Syntax.Syntax       (Domain (..), Syntax)
import qualified Syntax.Syntax
import           Syntax.Term
import           Term
import           Token

import           Control.Applicative (Alternative (..))
import           Data.Maybe          (fromJust, isJust)

class Alternative f => Parser f where
  match :: (Token -> Bool) -> f Token
  mark :: String -> f a
  sourced :: f a -> f (Sourced a)

-- Wrap to avoid overlapping Syntax and Domain instances
newtype T f a = T { unT :: f a }

instance Parser f => Syntax (T f) where
  f <$> T p = T (construct f <$> p)
  T p <*> T q = T ((,) <$> p <*> q)
  empty = T empty
  T p <|> T q = T (p <|> q)
  pure = T . pure
  match f _ = T $ fromJust . f <$> match (isJust . f)
  mark = T . mark
  unparseable = const (T empty)

instance Parser f => Domain (T f) Parse where
  annotated (T p) = T $ (\(s :< p) -> (s, ()) :< p) <$> sourced p
  combine _ f (p, q) = (view source p <> view source q, ()) :< f (p, q)

parse :: forall a f. (Recursive a, Parser f) => f (Annotated Parse a)
parse = unT (annotated (syntax (witness :: I a)))
