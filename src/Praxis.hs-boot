{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Praxis
  ( Praxis
  )
  where

import           Control.Monad.Trans.Maybe (MaybeT)
import           Control.Monad.Trans.State (StateT)

data PraxisState

type Praxis = MaybeT (StateT PraxisState IO)
