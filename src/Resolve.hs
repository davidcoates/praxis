module Resolve
  (
  ) where

import           AST
import           Parse
import           Source

data ResolverError = UnknownName String Source

instance Show ResolverError where
  show (UnknownName s p) = "Unknown name '" ++ s ++ "' at " ++ show p


-- resolve :: Praxis Exp -> Either ResolverError (Praxis Exp)
