{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Lower
  ( run
  , Lowering
  ) where

import           Common
import           Introspect
import qualified Lower.Lift         as Lift
import qualified Lower.Linearize    as Linearize
import qualified Lower.Monomorphize as Monomorphize
import           Praxis
import           Stage
import           Term


type family Lowering a where
  Lowering Program = Annotated Lower Program
  Lowering Exp     = (Annotated Lower Program, Annotated Lower Exp)

run :: IsTerm a => Annotated TypeCheck a -> Praxis (Lowering a)
run term = case typeof (view value term) of
  ProgramT -> do
    prog <- Monomorphize.run term
    prog <- Lift.run prog
    Linearize.run prog
  ExpT -> do
    (prog, exp) <- Monomorphize.run term
    prog        <- Lift.run prog
    (prog, exp) <- Lift.runExp prog exp
    prog        <- Linearize.run prog
    exp         <- Linearize.runExp exp
    return (prog, exp)
