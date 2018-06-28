-- Type checker

module Check
  ( check
  ) where

import Check.AST
import Check.Generate (generate)
import Check.Solve (solve)
import Compiler
import Error
import Inbuilts (inbuilts, TopDecl(..))
import Record
import Tag
import Type

import Env.TEnv (TEnv)
import qualified Env.TEnv as TEnv
import Env.QTEnv (QTEnv)
import qualified Env.QTEnv as QTEnv

initialQTEnv :: QTEnv
initialQTEnv = QTEnv.fromList $ map (\(s, t) -> (s, ty t)) inbuilts

-- TODO move this somewhere else
initialTEnv :: TEnv
initialTEnv = TEnv.fromList
  [ ("add", t)
  , ("mul", t)
  , ("sub", t)
  , ("putInt", TyFun (TyPrim TyInt) (TyUnit :# singleton (EfLit "StdOut")))
  , ("getInt", TyFun TyUnit (TyPrim TyInt :# singleton (EfLit "StdIn")))
  , ("putStrLn", TyFun (TyPrim TyString) (TyUnit :# singleton (EfLit "StdOut")))
  ]
  where t = TyFun (TyRecord (pair (TyPrim TyInt) (TyPrim TyInt))) (TyPrim TyInt :# empty)

check :: Compiler ()
check = setIn stage Check $ setIn tEnv initialTEnv $ setIn qtEnv initialQTEnv $ do
  cs <- generate
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  e <- get typedAST
  let e' = tagMap (\(t, s) -> (subsType ft fe <$> t, s)) e
  debugPrint e'
  set typedAST e'

