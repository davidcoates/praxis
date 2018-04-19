module Check.AST
  ( AST
  , Annotation
  , Annotated
  , module AST
  ) where

import AST
import Type
import Source (Source)

type Annotation = (Type, Source)
type Annotated a = a Annotation
type AST = Annotated Exp
