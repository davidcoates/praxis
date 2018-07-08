{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Check
  ( Checkable(..)
  ) where

import qualified Parse.Parse.AST as Parse (Annotated)
import           Praxis          (Praxis, Stage (..), save, stage)
import           Type            (Kinded, Type)

class Checkable a b | a -> b where
  check :: a -> Praxis b
  check p = save stage $ do
    set stage Check
    p' <- check' p
    return p'
  check' :: a -> Praxis b

instance Checkable (Parse.Annotated Type) (Kinded Type)
