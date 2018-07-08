{-# LANGUAGE RankNTypes #-}

module Check.AST
  ( Annotation
  , Annotated(..)
  , Impure
  , module AST
  ) where

import           AST
import           Source (Source)
import           Tag    (Tagged)
import           Type   (Impure, Kinded)

-- TODO Impure shouldn't really have a kind
type Annotation = (Maybe (Kinded Impure), Source)

type Annotated a = Tagged Annotation a
