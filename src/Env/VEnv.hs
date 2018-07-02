module Env.VEnv
  ( VEnv
  , fromList

  , elim
  , elimN
  , intro
  , lookup
  )
where

import           Common  (Name)
import           Env     (VEnv)
import           Env.Env (Env, fromList)
import qualified Env.Env as Env
import           Praxis
import           Value

import           Prelude hiding (lookup)


elim :: Praxis ()
elim = do
  l <- get vEnv
  set vEnv (Env.elim l)

elimN :: Int -> Praxis ()
elimN n = do
  l <- get vEnv
  set vEnv (Env.elimN n l)

intro :: Name -> Value -> Praxis ()
intro n v = over vEnv (Env.intro n v)

lookup :: Name -> Praxis (Maybe Value)
lookup n = do
  l <- get vEnv
  return (Env.lookup n l)
