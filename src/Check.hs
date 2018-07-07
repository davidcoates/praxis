{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Check
  ( Checkable(..)
  ) where

import           Check.AST
import           Check.Generate
import           Check.Solve     (solve)
import qualified Parse.Parse.AST as Parse (Annotated)
import           Praxis
import           Tag
import           Type            (sub)

import           Control.Arrow   (first)
import           Prelude         hiding (log)

class Checkable a where
  check :: Parse.Annotated a -> Praxis (Annotated a)

instance (Show (Annotated a), TagTraversable a, Generatable a) => Checkable a where
  check p = save stage $ do
    set stage Check
    (p', cs) <- generate p
    solution <- solve cs
    let p'' = tagMap (first (sub (`lookup` solution) <$>)) p'
    log Debug p''
    return p''
