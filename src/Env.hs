module Env
  ( VEnv
  , TEnv
  , KEnv
  ) where

import           Common   (Name)
import           Env.AEnv (AEnv)
import           Env.Env  (Env)
import           Type     (Kind, Kinded, QType)
import           Value    (Value)

type VEnv = Env Name Value

type TEnv = AEnv Name (Kinded QType)

type KEnv = Env Name Kind
