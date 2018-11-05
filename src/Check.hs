module Check
  ( Checkable(..)
  ) where

import           AST
import           Check.Annotate
import           Check.Generate
import           Check.System
import           Common
import           Parse.Annotate
import qualified Parse.Parse.AST as Parse (Annotated)
import           Praxis
import           Record
import           Type

import           Control.Arrow   (first)
import           Data.Maybe      (fromMaybe)
import qualified Data.Set        as Set
import           Prelude         hiding (log)

class Checkable a where
  check :: Parsed a -> Praxis (Kinded a)

instance Checkable Program where
  check = undefined

{-
  check p = save stage $ do
    put stage Check
    put system initialSystem
    p' <- check' p
    return p'
  check' :: a -> Praxis b
-}

{-
checkWithSub :: (Show (Annotated b), TagTraversable b, Generatable a (Annotated b)) => a -> Praxis (Annotated b)
checkWithSub p = do
  p' <- generate p
  sol <- solve
  let f g (t, e, s) = (g <$> t, g <$> e, s)
      p'' = tagMap (f (fullSol sol)) p'
  log Debug p''
  return p''

fullSol :: (KindTraversable a, TypeTraversable a) => ([(Name, Kinded Type)], [(Name, Kind)]) -> a -> a
fullSol (tySol, kindSol) = subs f . subs (`lookup` tySol) . subs (`lookup` kindSol)
  where f :: (Kind, Name) -> Maybe (Kinded Type) -- Trivial defaulting
        f (k, n) = if head n /= '?' then Nothing else (k :<) <$> case k of -- TODO fix the /= '?' hack
          KindEffect -> Just $ TyEffects Set.empty
          KindType   -> Just $ TyRecord Record.unit
          _          -> Nothing

{- TODO actually use this
checkNoUnis :: (KindTraversable a, TypeTraversable a) => a -> Praxis ()
checkNoUnis p = if null (extract (unis :: Kind -> [Name]) p ++ extract (unis :: Kinded Type -> [Name]) p) then pure () else error "checkNoUnis TODO a proper error"
-}

instance Checkable (Parse.Annotated Program) (Annotated Program) where
  check' = checkWithSub

instance Checkable (Parse.Annotated Exp) (Annotated Exp) where
  check' = checkWithSub

instance Checkable (Parse.Annotated Type) (Kinded Type) where
  check' p = do
    p' <- generate p
    sol <- solve
    let p'' = fullSol sol p'
    log Debug p''
    return p''


-}
