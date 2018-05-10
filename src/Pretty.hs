module Pretty
  ( indent
  , indents
  , TreeString(..)
  , Tree(..)
  , showTree
  , treeRec
  , treeRecWith
  ) where

import Data.Tree (Tree(..), drawTree)
import Data.Tree.Pretty (drawVerticalTree)
import Tag
import Source

indent :: String -> String
indent = indents . lines

indents :: [String] -> String
indents = unlines . map ("  " ++)

class TreeString a where
  treeString :: a -> Tree String

showTree :: TreeString a => a -> String
showTree = strip . drawVerticalTree . treeString
  where strip []     = ""
        strip ['\n'] = ""
        strip [x]    = [x]
        strip (x:xs) = x : strip xs

treeRec :: Show a => (b (Tag a) -> Tree String) -> Tagged a b -> Tree String
treeRec = treeRecWith show

treeRecWith :: (a -> String) -> (b (Tag a) -> Tree String) -> Tagged a b -> Tree String
treeRecWith sh f (a :< x) = case f x of Node n bs -> Node (n ++ " @ " ++ sh a) bs
