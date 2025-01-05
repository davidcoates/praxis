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
import qualified Parse.Tokenize as Tokenize
import           Praxis
import           Stage
import           Term

-- | A wrapper which runs tokenize, parse, desugar, and rewrite
parse :: forall a. Term a => String -> Praxis (Annotated a)
parse text = save stage $ do
  stage .= Parse
  let topLevel = case witness :: I a of { IProgram -> True; _ -> False }
  tokens <- Tokenize.run topLevel text
  Parse.run tokens >>= Desugar.run
