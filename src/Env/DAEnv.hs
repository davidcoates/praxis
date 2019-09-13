{-# LANGUAGE OverloadedStrings #-}

module Env.DAEnv
  ( DAEnv
  , fromList

  , intro
  , get
  )
where

import           Common
import           Env.Env (fromList)
import qualified Env.Env as Env
import           Praxis
import           Term

intro :: Name -> Typed DataAlt -> Praxis ()
intro n v = daEnv %= Env.intro n v

get :: Source -> Name -> Praxis (Typed DataAlt)
get s n = do
  l <- use daEnv
  case Env.lookup n l of
    Just v  -> return v
    Nothing -> throwAt s $ "data constructor " <> quote (plain n) <> " is not in scope"
