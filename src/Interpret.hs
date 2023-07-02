{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}

module Interpret
  ( interpret
  , interpretFile
  ) where

import           Check           (check)
import           Common
import           Interpret.Eval
import           Interpret.Value (Value)
import           Introspect
import           Parse           (parse)
import           Praxis
import           Term

interpretFile :: Evaluable a b => Praxis (Annotated a, b)
interpretFile = do
  f <- use infile
  case f of
    Nothing -> throw "msising infile"
    Just f  -> liftIO (readFile f) >>= interpret

interpret :: forall a b. Evaluable a b => String -> Praxis (Annotated a, b)
interpret s = do
  x <- parse s :: Praxis (Annotated a)
  y <- check x
  v <- eval y
  return (y, v)
