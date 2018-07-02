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
import           Type            (subsImpure)

import           Prelude         hiding (log)

class Checkable a where
  check :: Parse.Annotated a -> Praxis (Annotated a)

instance (Show (Annotated a), TagTraversable a, Generatable a) => Checkable a where
  check p = save stage $ do
    set stage Check
    (p', cs) <- generate p
    subs <- solve cs
    let ft x = lookup x subs
    let fe x = Nothing
    let p'' = tagMap (\(t, s) -> (subsImpure ft fe <$> t, s)) p'
    log Debug p''
    return p''
