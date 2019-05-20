{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module Print
  (
  ) where

import           Common
import           Introspect
import           Syntax.Unparser
import           Token

import           Data.Maybe      (fromJust)

newtype Printer a = Printer { runPrinter :: a -> Maybe [Token] }

force :: Printer a -> a -> [Token]
force (Printer f) x = case f x of
  Nothing -> []
  Just xs -> xs

instance Unparser Printer where
  f >$< g = Printer $ \x -> case f x of
    Nothing -> Nothing
    Just y  -> Just (force g y)
  f >*< g = Printer $ \(a, b) -> Just $ force f a ++ force g b
  empty = Printer $ const Nothing
  Printer f <|> Printer g = Printer $ \x -> case f x of
    Nothing -> g x
    Just xs -> Just xs
  token = Printer $ \x -> Just [x]
  mark s = Printer (error s)
  annotated f = Printer $ \x -> let
    body  = force f (view value x)
    constraint = display (view source x) (\s -> "[" ++ show (start s) ++ "]") ++ body ++ display (label x) id
    display s f = if s == mempty then [] else [Print (f s)]
      in Just $ case typeof x of
    ITypeConstraint -> constraint
    IKindConstraint -> constraint
    _               -> display (label x) (\l -> "[" ++ l ++ "]") ++ body

unlayout :: [Token] -> String
unlayout ts = unlayout' (-1) ts where
  unlayout' n ts = case ts of
    []               -> ""
    Special '{' : ts -> (if n >= 0 then "\n" ++ replicate (n+1) '\t' else "") ++ unlayout' (n+1) ts
    Special ';' : ts -> "\n" ++ replicate n '\t' ++ unlayout' n ts
    Special '}' : ts -> unlayout' (n-1) ts
    [t]              -> show t
    t : ts           -> show t ++ " " ++ unlayout' n ts

instance (Complete s, Recursive a, x ~ Annotation s a) => Show (Tag (Source, x) (a s)) where
  show = unlayout . force unparse
