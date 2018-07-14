{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Check
  ( Checkable(..)
  , Annotated
  ) where

import           Check.AST
import           Check.Generate
import           Check.Solve     (solve)
import qualified Parse.Parse.AST as Parse (Annotated)
import           Praxis
import           Record
import           Tag
import           Type            (Kind (..), KindTraversable (..), Kinded,
                                  Type (..), TypeTraversable (..))

import           Control.Arrow   (first)
import           Data.Maybe      (fromMaybe)
import qualified Data.Set        as Set
import           Prelude         hiding (log)

class Checkable a b | a -> b where
  check :: a -> Praxis b
  check p = save stage $ do
    set stage Check
    p' <- check' p
    return p'
  check' :: a -> Praxis b

checkWithSub :: (Show (Annotated b), TagTraversable b, Generatable a (Annotated b)) => a -> Praxis (Annotated b)
checkWithSub p = do
  (p', cs) <- generate p
  sol <- solve cs
  let p'' = tagMap (first (fullSol sol <$>)) p'
  log Debug p''
  return p''

fullSol :: (KindTraversable a, TypeTraversable a) => ([(Name, Kinded Type)], [(Name, Kind)]) -> a -> a
fullSol (tySol, kindSol) = tySubWithKind f . tySub (`lookup` tySol) . kindSub (`lookup` kindSol)
  where f (k, n) = (k :<) <$> case k of
          KindEffect -> Just $ TyEffects Set.empty
          KindType   -> Just $ TyRecord Record.unit
          _          -> Nothing

checkNoUnis :: (KindTraversable a, TypeTraversable a) => a -> Praxis ()
checkNoUnis p = if null (kindUnis p ++ tyUnis p) then pure () else error "checkNoUnis TODO a proper error"

instance Checkable (Parse.Annotated Program) (Annotated Program) where
  check' = checkWithSub

instance Checkable (Parse.Annotated Exp) (Annotated Exp) where
  check' = checkWithSub

instance Checkable (Parse.Annotated Type) (Kinded Type) where
  check' p = do
    (p', cs) <- generate p
    sol <- solve cs
    let p'' = fullSol sol p'
    log Debug p''
    return p''

