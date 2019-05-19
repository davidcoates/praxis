{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax.Type where

import           Syntax.TH
import           Type

definePrisms ''Constraint
