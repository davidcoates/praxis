module Check.Type.Require
  ( require
  , requires
  , our

  , module Check.Require
  ) where

import           Check.Require

import           Check.System      hiding (System)
import           Check.Type.Reason
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Term

require :: Annotated TyProp -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Annotated TyProp] -> Praxis ()
requires = mapM_ require

our :: Lens' PraxisState System
our = system . tySystem
