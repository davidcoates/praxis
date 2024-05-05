{-# LANGUAGE TemplateHaskell #-}

module Translate.State
  ( State(..)
  , emptyState

  , llvmModule
  ) where

import           Common
import           Control.Lens               (makeLenses)
import qualified LLVM.Codegen.ModuleBuilder as LLVM


data State = State
  { _llvmModule :: LLVM.Module
  }

emptyState :: State
emptyState = State
  { _llvmModule = LLVM.Module []
  }

makeLenses ''State
