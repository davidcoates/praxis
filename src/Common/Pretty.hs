module Common.Pretty
  ( indent
  , indents
  ) where

indent :: String -> String
indent = indents . lines

indents :: [String] -> String
indents = unlines . map ("  " ++)

