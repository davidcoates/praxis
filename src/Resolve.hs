{-# LANGUAGE OverloadedStrings #-}

module Resolve
  (
  ) where

import           AST
import           Common
import           Parse

data ResolverError = UnknownName String Source

instance Pretty ResolverError where
  pretty (UnknownName s p) = "Unknown name '" <> plain s <> "' at " <> pretty p


-- resolve :: Praxis Exp -> Either ResolverError (Praxis Exp)
