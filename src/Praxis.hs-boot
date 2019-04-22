{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Praxis
  ( Praxis
  )
  where

import           Control.Monad.Except (ExceptT)
import           Control.Monad.State  (StateT)

data PraxisState

type Praxis = ExceptT String (StateT PraxisState IO)
