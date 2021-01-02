module Check.Kind.Require
  ( require
  , requires
  , our

  , module Check.Require
  ) where

import           Check.Require

import           Check.Kind.Reason
import           Check.Kind.System
import           Check.System      hiding (System)
import           Common
import           Introspect
import           Praxis
import           Term

require :: Annotated KindProp -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Annotated KindProp] -> Praxis ()
requires = mapM_ require

our :: Lens' PraxisState System
our = system . kindSystem
