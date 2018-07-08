{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Interpret
  ( Interpretable(..)
  ) where

import           AST
import           Check  (Annotated, check)
import           Eval
import           Parse  (parse)
import qualified Parse  (Annotated)
import           Praxis
import           Value  (Value)

class Evaluable a b => Interpretable a b where
  interpret :: String -> Praxis (a, b)
  interpretFile :: FilePath -> Praxis (a, b)
  interpretFile f = do
    set filename f
    s <- liftIO (readFile f)
    interpret s

instance Interpretable (Annotated Program) () where
  interpret s = do
    x <- parse s :: Praxis (Parse.Annotated Program)
    y <- check x :: Praxis (Annotated Program)
    v <- eval y
    return (y, v)

instance Interpretable (Annotated Exp) Value where
  interpret s = do
    x <- parse s :: Praxis (Parse.Annotated Exp)
    y <- check x :: Praxis (Annotated Exp)
    v <- eval y
    return (y, v)
