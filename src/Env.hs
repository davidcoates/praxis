module Env
  ( VEnv
  , TEnv
  , KEnv
  ) where

import           Common   (Name)
import           Env.Env  (Env)
import           Env.LEnv (LEnv)
import           Type     (Kind, Kinded, QType)
import           Value    (Value)

type VEnv = Env Name Value

type TEnv = LEnv Name (Kinded QType)

type KEnv = Env Name Kind
