{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}

module Print
  (
  ) where

import           Common
import           Introspect
import           Pretty
import           Syntax.Unparser
import           Term
import           Token

newtype Printer a = Printer { runPrinter :: a -> Maybe [Token] }

force :: Printer a -> a -> [Token]
force (Printer f) x = case f x of
  Nothing -> []
  Just xs -> xs

instance Unparser Printer where
  f >$< g = Printer $ \x -> case f x of
    Nothing -> Nothing
    Just y  -> Just $ force g y
  f >*< g = Printer $ \(a, b) -> Just $ force f a ++ force g b
  empty = Printer $ const Nothing
  Printer f <|> Printer g = Printer $ \x -> case f x of
    Nothing -> g x
    Just xs -> Just xs
  token = Printer $ \x -> Just [x]
  mark s = Printer (error s)
  annotated f = Printer $ \x -> let
    body  = force f (view value x)
    constraint = (if view source x == Phantom then [] else [Print ("[" <> pretty (show (view source x)) <> "]")]) ++ body ++ [Print (label (typeof (view value x)) (view annotation x))]
      in Just $ case typeof (view value x) of
    ITypeConstraint -> constraint
    IKindConstraint -> constraint
    i               -> [Print (cmap (\c -> if null c then Nil else "[" <> c <> "]") (label i (view annotation x)))] ++ body

indent :: Int -> Printable String
indent n
  | n <= 0    = "\n" -- TODO why are we getting -1?
  | otherwise = indent (n-1) <> "    "

unlayout :: [Token] -> Printable String
unlayout ts = unlayout' (-1) ts where
  unlayout' n ts = case ts of
    []      -> ""
    Special t : ts
      | t == '{' -> (if n >= 0 then indent (n+1) else blank) <> unlayout' (n+1) ts
      | t == ';' -> indent n <> unlayout' n ts
      | t == '}' -> unlayout' (n-1) ts
    [t]    -> pretty t
    t : ts -> cmap (\c -> if null c then Nil else c <> " ") (pretty t) <> unlayout' n ts

instance (Recursive a, x ~ Annotation a) => Pretty (Tag (Source, Maybe x) a) where
  pretty = unlayout . force unparse

label :: Recursive a => I a -> Maybe (Annotation a) -> Printable String
label _ Nothing  = blank
label i (Just a) = case i of
  IExp            -> prettyIf Types a
  IPat            -> prettyIf Types a
  ITyPat          -> prettyIf Kinds a
  IType           -> prettyIf Kinds a
  ITypeConstraint -> pretty a
  IKindConstraint -> pretty a
  IDataAlt        -> pretty a
  _               -> blank
