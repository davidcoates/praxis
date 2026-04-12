{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Lower
  ( run
  , Lowering
  ) where

import           Common
import           Introspect
import qualified Lower.LambdaLift   as LambdaLift
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
    LambdaLift.run prog
  ExpT -> do
    (prog, exp) <- Monomorphize.run term
    prog'       <- LambdaLift.run prog
    LambdaLift.runExp prog' exp
