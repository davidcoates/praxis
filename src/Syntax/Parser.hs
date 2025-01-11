{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Syntax.Parser
  ( Parser(..)
  , parse
  ) where

import           Common
import           Introspect
import           Stage
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
  expected :: String -> f a
  sourced :: f a -> f (Sourced a)

newtype T f a = T { unT :: f a }

instance Parser f => Syntax (T f) where
  f <$> T p = T (construct f <$> p)
  T p <*> T q = T ((,) <$> p <*> q)
  empty = T empty
  T p <|> T q = T (p <|> q)
  pure = T . pure
  match f _ = T $ fromJust . f <$> match (isJust . f)
  expected = T . expected
  internal = const (T empty)
  annotated (T p) = T $ (\(s :< p) -> (s, Nothing) :< p) <$> sourced p

parse :: forall f s a. (Parser f, IsTerm a, IsStage s) => f (Annotated s a)
parse = unT (Syntax.annotated (syntax (termT :: TermT a)))
