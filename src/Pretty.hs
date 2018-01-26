module Pretty
  ( indent
  ) where

indent :: String -> String
indent = unlines . map ("  " ++) . lines
