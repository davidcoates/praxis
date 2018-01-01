module Resolver
  (
  ) where

import AST
import Parse

data ResolverError = UnknownName String SourcePos

instance Show ResolverError where
  show (UnknownName s p) = "Unknown name '" ++ s ++ "' at " ++ show p


-- resolve :: Praxis Exp -> Either ResolverError (Praxis Exp)

