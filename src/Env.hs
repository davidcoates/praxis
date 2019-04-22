module Env
  ( VEnv
  , TEnv
  , KEnv
  ) where

import           Annotate
import           Common
import           Env.Env  (Env)
import           Env.LEnv (LEnv)
import           Kind     (Kind)
import           Type     (QType)
import           Value    (Value)

type VEnv = Env Name Value

type TEnv = LEnv Name (Typed QType)

type KEnv = Env Name (Kinded Kind)
