{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Parse
  ( run
  ) where

import           Common
import           Introspect
import qualified Parse.Desugar
import qualified Parse.Parse
import qualified Parse.Tokenize
import           Praxis
import           Stage
import           Term


-- | A wrapper which runs tokenise, parse, desugar, and rewrite
run :: forall a. Term a => String -> Praxis (Annotated a)
run text = save stage $ do
  stage .= Parse
  let topLevel = case witness :: I a of { IProgram -> True; _ -> False }
  tokens <- Parse.Tokenize.run topLevel text
  Parse.Parse.run tokens >>= Parse.Desugar.run
