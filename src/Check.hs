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
import           Tag
import           Type            (KindTraversable (..), Kinded, Type,
                                  TypeTraversable (..))

import           Control.Arrow   (first)
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
  solution <- solve cs
  let p'' = tagMap (first (tySub (`lookup` solution) <$>)) p'
  log Debug p''
  return p''

instance Checkable (Parse.Annotated Program) (Annotated Program) where
  check' = checkWithSub

instance Checkable (Parse.Annotated Exp) (Annotated Exp) where
  check' = checkWithSub

instance Checkable (Parse.Annotated Type) (Kinded Type) where
  check' p = do
    (p', cs) <- generate p
    log Debug p'
    return p'
