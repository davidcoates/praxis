module Check.AST
  ( AST
  , Annotated
  , module AST
  ) where

import AST
import Type
import Source
import Tag

type Annotated a = Tagged (Maybe Type, Source) a

type AST = Annotated Program
