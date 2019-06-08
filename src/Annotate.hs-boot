{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Annotate
  ( Parse
  , TypeCheck
  , KindCheck
  , Annotation
  , Annotated
  , Derivation(..)
  ) where

import           Common

data Parse
data TypeCheck
data KindCheck

type family Annotation a (b :: * -> *) where ..

type Annotated a b = Tag (Source, Annotation a b) (b a)

data Derivation s a = Root String
                    | Antecedent (Annotated s a)
