{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Praxis
  ( Praxis
  , PraxisState
  , internalError
  )
  where

import           Error                (Error)

import           Control.Monad.Except (ExceptT)
import           Control.Monad.State  (StateT)

data PraxisState

type Praxis = ExceptT Error (StateT PraxisState IO)

internalError :: String -> a
