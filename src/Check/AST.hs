module Check.AST
  ( AST
  , Annotation
  , Annotated
  , module AST
  ) where

import AST
import Type
import Pos

type Annotation = (Type, Pos)
type Annotated a = a Annotation
type AST = Annotated Exp
