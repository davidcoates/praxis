{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Check.Generate
  ( Generatable(..)
  ) where

import           AST            (Program)
import           Check.Annotate
import           Common
import           Parse.Annotate
import           Praxis
import           Stage

-- Show (Kinded a) =>
class Generatable s t a where
  generate' :: (Annotated s a) -> Praxis (Annotated t a)
  generate  :: (Annotated s a) -> Praxis (Annotated t a)
  generate p = undefined
{-
  generate p = save stage $ do
    put stage Generate
    p' <- generate' p
    log Debug p'
    cs <- get (system . constraints)
    let cs' = nub . sort $ cs
    logList Debug cs
    return p'
-}

instance Generatable Parse KindCheck Program where
  generate' = undefined

{-
instance Generatable (Parse.Annotated Program) (Annotated Program) where
  generate' = program

instance Generatable (Parse.Annotated Exp) (Annotated Exp) where
  generate' = exp

instance Generatable (Parse.Annotated Type) (Kinded Type) where
  generate' = typ
-}
