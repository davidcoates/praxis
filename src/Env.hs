module Env
  ( VEnv
  , TEnv
  , KEnv
  , DAEnv
  ) where

import           Common
import           Env.Env  (Env)
import           Env.LEnv (LEnv)
import           Term
import           Value    (Value)

type VEnv = Env Name Value

type TEnv = LEnv Name (Typed QType)

type KEnv = Env Name (Kinded Kind)

type DAEnv = Env Name (Typed DataAlt)
