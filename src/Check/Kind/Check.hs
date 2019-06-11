module Check.Kind.Check
  ( check
  ) where

import           Check.Kind.Generate
import           Check.Kind.Require
import           Check.Kind.Solve
import           Check.Kind.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Recursive a => Parsed a -> Praxis (Kinded a)
check a = save stage $ do
  stage .= KindCheck Warmup
  our .= initialSystem
  a' <- generate a
  ks <- solve
  return $ sub (\k -> case k of { KindUni n -> lookup n ks; _ -> Nothing }) a'
