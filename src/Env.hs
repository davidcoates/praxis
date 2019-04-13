module Env
  ( VEnv
  , TEnv
  , KEnv
  ) where

import           Common
import           Env.Env  (Env)
import           Env.LEnv (LEnv)
import           Stage
import           Type     (Kind, QType)
import           Value    (Value)

type VEnv = Env Name Value

type TEnv = LEnv Name (Annotated TypeCheck QType)

type KEnv = Env Name (Annotated KindCheck Kind)
