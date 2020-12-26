{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Praxis
  ( Praxis
  , liftIOUnsafe
  )
  where

import           Common

data PraxisState

type Praxis = MaybeT (StateT PraxisState IO)

liftIOUnsafe :: IO a -> Praxis a
