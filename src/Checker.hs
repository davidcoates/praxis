-- Type checker

module Checker
  (
  ) where

import AST hiding (Praxis)
import Type

type Praxis a = Annotate (Type, SourcePos) a


-- infer :: Annotate SourcePos Exp -> Either TypeError (Praxis Exp)
-- infer = 
