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
import Tag

infer :: Compiler TypeError ()
infer = do
  cs <- generate
  ((t, s) :< e) <- get typedAST
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  let e' = (subsType ft fe t, s) :< e
  set typedAST e'

-- TODO: Do we need to check no unification variables left?
