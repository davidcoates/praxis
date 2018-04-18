module Parse.Desugar.AST
  ( module AST
  , AST
  ) where

import AST
import Source (Source)

type Annotation = Source
type Annotated a = a Annotation

type AST = Annotated Exp
