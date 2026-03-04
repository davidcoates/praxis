{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Monomorphize
  ( run
  , Monomorphization(..)
  ) where

import           Common
import           Introspect
import           Monomorphize.State
import           Praxis
import           Stage
import           Term


type family Monomorphization a where
  Monomorphization Program = Annotated Monomorphize Program
  Monomorphization Exp = (Annotated Monomorphize Program, Annotated Monomorphize Exp)

run :: IsTerm a => Annotated TypeCheck a -> Praxis (Monomorphization a)
run term = monomorphize term

monomorphize :: IsTerm a => Annotated TypeCheck a -> Praxis (Monomorphization a)
monomorphize term = case typeof (view value term) of

  ExpT -> do
    exp <- monomorphizeExp term
    program <- getProgram
    return (program, exp)

  ProgramT -> do
    monomorphizeProgram term
    getProgram

  where
    getProgram :: Praxis (Annotated Monomorphize Program)
    getProgram = do
      decls <- use (monomorphizeState . exportedDecls)
      monomorphizeState . exportedDecls .= []
      return (phantom (Program decls))

monomorphizeExp :: Annotated TypeCheck Exp -> Praxis (Annotated Monomorphize Exp)
monomorphizeExp _ = error "TODO: monomorphizeExp"

monomorphizeProgram :: Annotated TypeCheck Program -> Praxis ()
monomorphizeProgram _ = error "TODO: monomorphizeProgram"
