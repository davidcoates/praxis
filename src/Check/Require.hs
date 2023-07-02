{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module Check.Require
  ( newConstraint
  , implies
  , impliesProp
  ) where

import           Common
import           Term

newConstraint :: (Annotation (Prop a) ~ Derivation (Prop a), Show r) => a -> r -> Source -> Annotated (Prop a)
newConstraint c r s = (s, Just (Root (show r))) :< Exactly c

implies :: (Annotation (Prop a) ~ Derivation (Prop a)) => Annotated (Prop a) -> a -> Annotated (Prop a)
implies p c = p `impliesProp` Exactly c

impliesProp :: (Annotation (Prop a) ~ Derivation (Prop a)) => Annotated (Prop a) -> Prop a -> Annotated (Prop a)
impliesProp p1 p2 = let s = view source p1 in (s, Just (Antecedent p1)) :< p2

