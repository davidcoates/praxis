{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

module Common.Annotate
  ( Annotation
  , Annotated
  , source
  , annotation
  , Sourced
  ) where

import           Common.Misc
import           Common.Pretty
import           Common.Source
import           Common.Tag

type family Annotation a (b :: * -> *)

type Annotated a b = Tag (Source, Annotation a b) (b a)

-- These lenses are a bit more general so we can use them in a piecewise way
-- (where the intermedite value has an annotation and value which don't commute)
source :: Functor f => (Source -> f Source) -> Tag (Source, a) b -> f (Tag (Source, a) b)
source = tag . first

annotation :: Functor f => (a -> f b) -> Tag (Source, a) c -> f (Tag (Source, b) c)
annotation = tag . second

type Sourced a = Tag Source a

instance Pretty a => Pretty (Sourced a) where
  pretty (Phantom :< x) = pretty x
  pretty (a :< x)       = pretty a <> " " <> pretty x
