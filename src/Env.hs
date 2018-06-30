module Env
  ( QTEnv
  , TEnv
  , VEnv
  ) where

import           Common   (Name)
import           Env.AEnv (AEnv)
import           Env.Env  (Env)
import           Type     (Pure, QPure)
import           Value

type TEnv = AEnv Name Pure

type QTEnv = Env Name QPure

type VEnv = Env Name Value
