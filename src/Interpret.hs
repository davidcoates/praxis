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
    infile .= Just f
    term <- liftIO (readFile f)
    interpret term

instance Interpretable Program () where
  interpret text = do
    p <- parse text >>= check :: Praxis (Annotated Program)
    v <- eval p
    return (p, v)

instance Interpretable Exp Value where
  interpret text = do
    e <- parse text >>= check :: Praxis (Annotated Exp)
    v <- eval e
    return (e, v)
