module Check.Kind.Check
  ( check
  ) where

import           Check.Kind.Annotate
import           Check.Kind.Generate
import           Check.Kind.Require
import           Check.Kind.Solve
import           Check.Kind.System
import           Check.Type.Annotate
import           Common
import           Introspect
import           Praxis
import           Prelude             hiding (log)
import           Stage
import           Type

check :: Recursive a => Typed a -> Praxis (Kinded a)
check a = save stage $ do
  stage .= KindCheck Warmup
  our .= initialSystem
  a' <- generate a
  ks <- solve
  return $ sub (\k -> case k of { KindUni n -> lookup n ks; _ -> Nothing }) a'
