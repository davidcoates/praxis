{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Parse
  ( parse
  ) where

import           Common
import           Introspect
import qualified Parse.Desugar  as Desugar
import qualified Parse.Parse    as Parse
import qualified Parse.Tokenise as Tokenise
import           Praxis
import           Term

-- Tokenise, layout, parse, desugar
parse :: forall a. Term a => String -> Praxis (Annotated a)
parse text = do
  let topLevel = case witness :: I a of { IProgram -> True; _ -> False }
  tokens <- Tokenise.run topLevel text
  term <- Parse.run tokens
  Desugar.run term
