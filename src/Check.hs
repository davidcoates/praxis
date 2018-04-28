-- Type checker

module Check
  ( check
  ) where

import Check.AST
import Check.Generate (generate)
import Check.Solve (solve)
import Error
import Compiler
import Type
import Tag

check :: Compiler ()
check = do
  cs <- generate
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  e <- get typedAST
  let e' = tmap (\(t, s) -> (subsType ft fe t, s)) e
  debugPrint e'
  set typedAST e'

-- TODO: Do we need to check no unification variables left?
