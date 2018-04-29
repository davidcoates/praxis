module Parse.Desugar.AST
  ( module AST
  , AST
  , Annotated
  ) where

import AST
import Tag
import Source

type Annotated a = Tagged Source a

type AST = Annotated Program
