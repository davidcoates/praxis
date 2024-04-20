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
import           Stage
import           Term

-- | A wrapper which runs tokenise, parse, desugar, and rewrite
parse :: forall a. Term a => String -> Praxis (Annotated a)
parse text = save stage $ do
  stage .= Parse
  let topLevel = case witness :: I a of { IProgram -> True; _ -> False }
  tokens <- Tokenise.run topLevel text
  Parse.run tokens >>= Desugar.run >>= Rewrite.run
