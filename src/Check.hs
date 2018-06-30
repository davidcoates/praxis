-- Type checker

module Check
  ( check
  ) where

import           Check.AST
import           Check.Generate (generate)
import           Check.Solve    (solve)
import           Compiler
import           Error
import           Inbuilts       (TopDecl (..), inbuilts)
import           Record
import           Tag
import           Type

import           Env.QTEnv      (QTEnv)
import qualified Env.QTEnv      as QTEnv
import           Env.TEnv       (TEnv)
import qualified Env.TEnv       as TEnv

initialQTEnv :: QTEnv
initialQTEnv = undefined --QTEnv.fromList
  -- TODO effects
  -- [ ("dot", Forall [] ["a", "b", "c"] (TyFun (TyRecord (pair (TyFun (TyVar "a") (TyVar "b" :# empty), TyFun (TyVar "b") (TyVar "c" :# empty)))) (TyFun (TyVar "a") (TyVar "c" :# empty) :# empty)))
 --  ]
  -- TODO allow reading of types
  -- "forall a b c. (a -> b, b -> c) -> (a -> c)"
-- initialQTEnv = QTEnv.fromList $ map (\(s, t) -> (s, ty t)) inbuilts

-- TODO move this somewhere else (put all in the same place (fixity, value, type))
--
initialTEnv :: TEnv
initialTEnv = TEnv.fromList
  [ ("add", t)
  , ("mul", t)
  , ("sub", t)
  , ("putInt",   TyFun    (TyPrim TyInt) (TyRecord unit :# singleton (EfLit "StdOut")))
  , ("getInt",   TyFun   (TyRecord unit)  (TyPrim TyInt :# singleton (EfLit  "StdIn")))
  , ("putStrLn", TyFun (TyPrim TyString) (TyRecord unit :# singleton (EfLit "StdOut")))
  ]
  where t = TyFun (TyRecord (pair (TyPrim TyInt) (TyPrim TyInt))) (TyPrim TyInt :# empty)

check :: Compiler ()
check = save stage $ save tEnv $ save qtEnv $ do
  set stage Check
  set tEnv initialTEnv
  set qtEnv initialQTEnv
  cs <- generate
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  e <- get typedAST
  let e' = tagMap (\(t, s) -> (subsType ft fe <$> t, s)) e
  debugPrint e'
  set typedAST e'

