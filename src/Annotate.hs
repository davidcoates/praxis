{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module Annotate
  ( module Tag
  , Annotation
  , Annotated
  , source
  , annotation
  , Sourced
  ) where

import           Common
import           Control.Lens.Tuple (_1, _2)
import           Source
import           Tag

type family Annotation a (b :: * -> *)

type Annotated a b = Tag (Source, Annotation a b) (b a)

-- These lenses are a bit more general so we can use them in a piecewise way
-- (where the intermedite value has an annotation and value which don't commute)
source :: Functor f => (Source -> f Source) -> Tag (Source, a) b -> f (Tag (Source, a) b)
source = tag . _1

annotation :: Functor f => (a -> f b) -> Tag (Source, a) c -> f (Tag (Source, b) c)
annotation = tag . _2

type Sourced a = Tag Source a

-- TODO eventually use a pretty printer
instance Show (Tag (Source, a) b) where
  show = show . view (tag . _1)
