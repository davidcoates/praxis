{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module Common.Annotate
  ( Annotation
  , Annotated
  , source
  , annotation
  , Sourced
  ) where

import           Common.Misc
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
