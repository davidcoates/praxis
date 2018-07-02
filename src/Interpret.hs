{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Interpret
  ( Interpretable(..)
  ) where

import           AST
import           Check
import           Check.AST       (Annotated (..))
import           Eval
import           Parse
import qualified Parse.Parse.AST as Parse (Annotated (..))
import           Praxis

class Interpretable a where
  interpret :: String -> Praxis (Annotated a, Evaluation a)
  interpretFile :: FilePath -> Praxis (Annotated a, Evaluation a)
  interpretFile f = do
    set filename f
    s <- liftIO (readFile f)
    interpret s

instance (Parseable a, Checkable a, Evaluable a) => Interpretable a where
  interpret s = do
    x <- parse s
    y <- check x
    v <- eval y
    return (y, v)
