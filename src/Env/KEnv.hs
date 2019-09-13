module Env.KEnv
  ( KEnv
  , fromList

  , elim
  , elimN
  , intro
  , lookup
  )
where

import           Common
import           Env.Env (Env, fromList)
import qualified Env.Env as Env
import           Praxis
import           Term

import           Prelude hiding (lookup)

elim :: Praxis ()
elim = do
  l <- use kEnv
  kEnv .= Env.elim l

elimN :: Int -> Praxis ()
elimN n = do
  l <- use kEnv
  kEnv .= Env.elimN n l

intro :: Name -> Kinded Kind -> Praxis ()
intro n v = kEnv %= Env.intro n v

lookup :: Name -> Praxis (Maybe (Kinded Kind))
lookup n = do
  l <- use kEnv
  return (Env.lookup n l)
