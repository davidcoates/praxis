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
import           Stage
import           Type

check :: Recursive a => Typed a -> Praxis (Kinded a)
check a = save stage $ do
  stage .= KindCheck Warmup
  our .= initialSystem
  b <- generate a
  ks <- solve
  -- ksub (`lookup` ks)
  -- FIXME
  return undefined

{-
fullSol :: (KindTraversable a, TypeTraversable a) => ([(Name, Kinded Type)], [(Name, Kind)]) -> a -> a
fullSol (tySol, kindSol) = subs f . subs (`lookup` tySol) . subs (`lookup` kindSol)
  where f :: (Kind, Name) -> Maybe (Kinded Type) -- Trivial defaulting
        f (k, n) = if head n /= '?' then Nothing else (k :<) <$> case k of -- TODO fix the /= '?' hack
          KindEffect -> Just $ TyEffects Set.empty
          KindType   -> Just $ TyRecord Record.unit
          _          -> Nothing

checkNoUnis :: (KindTraversable a, TypeTraversable a) => a -> Praxis ()
checkNoUnis p = if null (extract (unis :: Kind -> [Name]) p ++ extract (unis :: Kinded Type -> [Name]) p) then pure () else error "checkNoUnis TODO a proper error"
-}
