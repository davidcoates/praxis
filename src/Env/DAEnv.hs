{-# LANGUAGE OverloadedStrings #-}

module Env.DAEnv
  ( DAEnv

  , get
  )
where

import           Common
import           Env
import           Praxis
import           Term
import Prelude hiding (lookup)

get :: Source -> Name -> Praxis (Typed DataAlt)
get s n = do
  l <- use daEnv
  case lookup n l of
    Just v  -> return v
    Nothing -> throwAt s $ "data constructor " <> quote (plain n) <> " is not in scope"
