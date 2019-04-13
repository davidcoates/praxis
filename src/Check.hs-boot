module Check
  ( Checkable(..)
  ) where

import           Check.Annotate (Kinded)
import           Parse.Annotate (Parsed)
import           Praxis         (Praxis)

class Checkable a where
  check :: Parsed a -> Praxis (Kinded a)
{-
  check p = save stage $ do
    put stage Check
    p' <- check' p
    return p'
  check' :: a -> Praxis b
-}
