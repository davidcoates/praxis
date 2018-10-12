module Env
  ( VEnv
  , TEnv
  , KEnv
  ) where

import           Annotate
import           Common   (Name)
import           Env.Env  (Env)
import           Env.LEnv (LEnv)
import           Stage
import           Type     (Kind, QType)
import           Value    (Value)

type VEnv = Env Name Value

type TEnv = LEnv Name (Annotated TypeCheck QType)

type KEnv = Env Name Kind
