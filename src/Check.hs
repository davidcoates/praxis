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
import Record

initialEnv :: Env
initialEnv = [ ("add", (t, 0))
             , ("mul", (t, 0))
             , ("sub", (t, 0))
             , ("putInt", (TyFun (TyPrim TyInt) (TyUnit :# singleton (EfLit "StdOut")), 0))
             , ("getInt", (TyFun TyUnit (TyPrim TyInt :# singleton (EfLit "StdIn")), 0))
             ]
  where t = TyFun (TyRecord (pair (TyPrim TyInt) (TyPrim TyInt))) (TyPrim TyInt :# empty)

check :: Compiler ()
check = do
  set tEnv initialEnv
  cs <- generate
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  e <- get typedAST
  let e' = tmap (\(t, s) -> (subsType ft fe <$> t, s)) e
  debugPrint e'
  set typedAST e'

-- TODO: Do we need to check no unification variables left?
