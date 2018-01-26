-- Type checker

module Check
  ( infer
  ) where

import Check.AST
import Check.Generate (generate)
import Check.Solve (solve)
import Check.Error
import Compile
import Type
import Control.Lens (over, _1)

infer :: Compiler TypeError ()
infer = do
  cs <- generate
  Just e <- get typedAST
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  let e' = over (annotation . _1) (subsType ft fe) e
  set typedAST (Just e')

-- TODO: Do we need to check no unification variables left?
