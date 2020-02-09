{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Interpret
  ( Interpretable(..)
  ) where

import           Check  (check)
import           Common
import           Eval
import           Parse  (parse)
import           Praxis
import           Term
import           Value  (Value)

class Evaluable a b => Interpretable a b where
  interpret :: String -> Praxis (Annotated a, b)
  interpretFile :: FilePath -> Praxis (Annotated a, b)
  interpretFile f = do
    filename .= f
    s <- liftIO (readFile f)
    interpret s

instance Interpretable Program () where
  interpret s = do
    x <- parse s :: Praxis (Annotated Program)
    y <- check x
    v <- eval y
    return (y, v)

instance Interpretable Exp Value where
  interpret s = do
    x <- parse s :: Praxis (Annotated Exp)
    y <- check x
    v <- eval y
    return (y, v)
