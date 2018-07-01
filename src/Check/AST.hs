module Check.AST
  ( AST
  , Annotated
  , module AST
  ) where

import           AST
import           Source
import           Tag
import           Type

type Annotated a = Tagged (Maybe Impure, Source) a

type AST = Annotated Program
