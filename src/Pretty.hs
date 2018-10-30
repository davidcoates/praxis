{-# LANGUAGE GADTs #-}

module Pretty
  ( indent
  , indents
  ) where

import           AST
import           Data.Tree        (Tree (..), drawTree)
import           Data.Tree.Pretty (drawVerticalTree)
import           Introspect
import           Record           (showKeys)
import qualified Record           (toList)
import           Source
import           Type

indent :: String -> String
indent = indents . lines

indents :: [String] -> String
indents = unlines . map ("  " ++)

