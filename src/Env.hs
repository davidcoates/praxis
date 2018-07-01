module Env
  ( TEnv
  , VEnv
  ) where

import           Common   (Name)
import           Env.AEnv (AEnv)
import           Env.Env  (Env)
import           Type     (Type)
import           Value

type TEnv = AEnv Name Type

type VEnv = Env Name Value
