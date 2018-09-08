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
import           Type   (Impure, Kinded, Type)

type Annotation = (Maybe (Kinded Type), Maybe (Kinded Type), Source)

type Annotated a = Tagged Annotation a
