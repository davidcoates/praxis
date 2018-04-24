module Pretty
  ( indent
  , indents
  , TreeString(..)
  , Tree(..)
  , showTree
  , treeRec
  ) where

import Data.Tree (Tree(..), drawTree)
import Tag
import Source

indent :: String -> String
indent = indents . lines

indents :: [String] -> String
indents = unlines . map ("  " ++)

class TreeString a where
  treeString :: a -> Tree String

showTree :: TreeString a => a -> String
showTree = strip . drawTree . treeString
  where strip []     = ""
        strip ['\n'] = ""
        strip [x]    = [x]
        strip (x:xs) = x : strip xs

treeRec :: Show a => (b (Tag a) -> Tree String) -> Tagged a b -> Tree String
treeRec f (a :< x) = case f x of Node n bs -> Node (n ++ " @ " ++ show a) bs
