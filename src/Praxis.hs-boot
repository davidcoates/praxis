{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Praxis
  ( Praxis
  )
  where

import           Common

data PraxisState

type Praxis = MaybeT (StateT PraxisState IO)
