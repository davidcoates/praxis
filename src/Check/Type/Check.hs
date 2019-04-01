module Check.Type.Check
  ( check
  ) where

import           Check.Type.Annotate
import           Check.Type.Generate
import           Check.Type.Require
import           Check.Type.Solve
import           Check.Type.System
import           Common
import           Introspect
import           Parse.Annotate
import           Praxis
import           Stage
import           Type

check :: Recursive a => Parsed a -> Praxis (Typed a)
check a = save stage $ do
  stage .= TypeCheck Warmup
  our .= initialSystem
  b <- generate a
  (ts, qs) <- solve
  let c = sub (\t -> case t of { TyUni n -> lookup n ts; _ -> Nothing }) b
  let d = sub (\q -> case q of { QTyUni n -> lookup n qs; _ -> Nothing }) c
  -- TODO log a b c d ts qs
  -- TODO FIXME add defaulting (need to wait until after kinds?)
  return d

{-
fullSol :: (KindTraversable a, TypeTraversable a) => ([(Name, Kinded Type)], [(Name, Kind)]) -> a -> a
fullSol (tySol, kindSol) = subs f . subs (`lookup` tySol) . subs (`lookup` kindSol)
  where f :: (Kind, Name) -> Maybe (Kinded Type) -- Trivial defaulting
        f (k, n) = if head n /= '?' then Nothing else (k :<) <$> case k of -- TODO fix the /= '?' hack
          KindType   -> Just $ TyRecord Record.unit
          _          -> Nothing

checkNoUnis :: (KindTraversable a, TypeTraversable a) => a -> Praxis ()
checkNoUnis p = if null (extract (unis :: Kind -> [Name]) p ++ extract (unis :: Kinded Type -> [Name]) p) then pure () else error "checkNoUnis TODO a proper error"
-}
