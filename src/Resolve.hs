module Resolve
  (
  ) where

import AST
import Parse
import Pos

data ResolverError = UnknownName String Pos

instance Show ResolverError where
  show (UnknownName s p) = "Unknown name '" ++ s ++ "' at " ++ show p


-- resolve :: Praxis Exp -> Either ResolverError (Praxis Exp)
