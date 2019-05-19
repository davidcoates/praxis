{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax.Kind where

import           Kind
import           Syntax.TH

definePrisms ''Constraint
