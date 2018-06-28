module Env.VEnv
  ( VEnv
  , fromList

  , elim
  , elimN
  , intro
  , lookup
  )
where

import Common (Name)
import Compiler
import Env (VEnv)
import Env.Env (Env, fromList)
import qualified Env.Env as Env
import Value

import Prelude hiding (lookup)


elim :: Compiler ()
elim = do
  l <- get vEnv
  set vEnv (Env.elim l)

elimN :: Int -> Compiler ()
elimN n = do
  l <- get vEnv
  set vEnv (Env.elimN n l)

intro :: Name -> Value -> Compiler ()
intro n v = over vEnv (Env.intro n v)

lookup :: Name -> Compiler (Maybe Value)
lookup n = do
  l <- get vEnv
  return (Env.lookup n l)
