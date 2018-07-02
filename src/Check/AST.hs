module Check.AST
  ( Annotation
  , Annotated(..)
  , module AST
  ) where

import           AST
import           Source
import           Tag
import           Type

type Annotation = (Maybe Impure, Source)

type Annotated a = Tagged Annotation a
