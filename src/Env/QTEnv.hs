module Env.QTEnv
  ( QTEnv
  , fromList

  , lookup
  )
where

import Common (Name)
import Compiler
import Env (QTEnv)
import Env.Env (Env, fromList)
import qualified Env.Env as Env
import Type (QPure)

import Prelude hiding (lookup)


lookup :: Name -> Compiler (Maybe QPure)
lookup n = do
  l <- get qtEnv
  return (Env.lookup n l)
