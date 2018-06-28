{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Compiler
  ( Compiler
  , CompilerState
  )
  where

import Error (Error)

import Control.Monad.Except (ExceptT)
import Control.Monad.State (StateT)

data CompilerState

type Compiler a = ExceptT Error (StateT CompilerState IO) a

