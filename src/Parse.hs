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
import qualified Parse.Rewrite  as Rewrite
import qualified Parse.Tokenise as Tokenise
import           Praxis
import           Term

-- | A wrapper which runs tokenise, layout, parse & desugar
parse :: forall a. Term a => String -> Praxis (Annotated a)
parse text = do
  let topLevel = case witness :: I a of { IProgram -> True; _ -> False }
  tokens <- Tokenise.run topLevel text
  term <- Parse.run tokens
  term <- Desugar.run term
  term <- Rewrite.run term
  return term
