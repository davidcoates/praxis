{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Interpret
  ( Interpretable(..)
  ) where

import           AST
import           Check          (check)
import           Check.Annotate
import           Common
import           Eval
import           Parse          (parse)
import           Parse.Annotate
import           Praxis
import           Value          (Value)

class Evaluable a b => Interpretable a b where
  interpret :: String -> Praxis (Kinded a, b)
  interpretFile :: FilePath -> Praxis (Kinded a, b)
  interpretFile f = do
    filename .= f
    s <- liftIO (readFile f)
    interpret s

instance Interpretable Program () where
  interpret s = do
    x <- parse s :: Praxis (Parsed Program)
    y <- check x :: Praxis (Kinded Program)
    v <- eval y
    return (y, v)

instance Interpretable Exp Value where
  interpret s = do
    x <- parse s :: Praxis (Parsed Exp)
    y <- check x :: Praxis (Kinded Exp)
    v <- eval y
    return (y, v)
