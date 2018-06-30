module Parse.Desugar.AST
  ( module AST
  , AST
  , Annotated
  ) where

import           AST
import           Source
import           Tag

type Annotated a = Tagged Source a

type AST = Annotated Program
