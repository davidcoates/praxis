{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

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
run :: forall a. IsTerm a => String -> Praxis (Annotated Parse a)
run text = do
  let topLevel = case termT :: TermT a of { ProgramT -> True; _ -> False }
  tokens <- Parse.Tokenize.run topLevel text
  Parse.Parse.run tokens >>= Parse.Desugar.run
