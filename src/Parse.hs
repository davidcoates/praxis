{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Parse
  ( parse
  ) where

import           Annotate
import           AST
import           Common
import           Introspect
import qualified Parse.Desugar  as Desugar
import qualified Parse.Parse    as Parse
import qualified Parse.Tokenise as Tokenise
import           Praxis

parse :: forall a. Recursive a => String -> Praxis (Parsed a)
parse s = do
  let top = case witness :: I a of { IProgram -> True; _ -> False }
  ts <- Tokenise.run top s
  p <- Parse.run ts
  Desugar.run p
