{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Syntax.Parser
  ( Parser(..)
  , parse
  ) where

import           Common
import           Introspect
import           Syntax.Prism
import qualified Syntax.Syntax       as Syntax
import           Syntax.Syntax       (Syntax)
import           Syntax.Term
import           Term
import           Token

import           Control.Applicative (Alternative (..))
import           Data.Maybe          (fromJust, isJust)

class Alternative f => Parser f where
  match :: (Token -> Bool) -> f Token
  mark :: String -> f a
  sourced :: f a -> f (Sourced a)

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
  annotated (T p) = T $ (\(s :< p) -> (s, Nothing) :< p) <$> sourced p

parse :: forall a f. (Term a, Parser f) => f (Annotated a)
parse = unT (Syntax.annotated (syntax (witness :: I a)))
