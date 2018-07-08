module Env.KEnv
  ( KEnv
  , fromList

  , elim
  , elimN
  , intro
  , lookup
  )
where

import           Common  (Name)
import           Env     (KEnv)
import           Env.Env (Env, fromList)
import qualified Env.Env as Env
import           Praxis
import           Type

import           Prelude hiding (lookup)


elim :: Praxis ()
elim = do
  l <- get kEnv
  set kEnv (Env.elim l)

elimN :: Int -> Praxis ()
elimN n = do
  l <- get kEnv
  set kEnv (Env.elimN n l)

intro :: Name -> Kind -> Praxis ()
intro n v = over kEnv (Env.intro n v)

lookup :: Name -> Praxis (Maybe Kind)
lookup n = do
  l <- get kEnv
  return (Env.lookup n l)
