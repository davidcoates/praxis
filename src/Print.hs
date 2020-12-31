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
  annotated f = Printer g where
    g x = Just $ case typeof (view value x) of
      ITypeConstraint -> constraint
      IKindConstraint -> constraint
      i               -> [Print (mapIfNotNull (\c -> "[" <> c <> "]") (label i (view annotation x)))] ++ body
      where
        body        = force f (view value x)
        constraint = (if view source x == Phantom then [] else [Print ("[" <> pretty (show (view source x)) <> "]")]) ++ body ++ [Print (label (typeof (view value x)) (view annotation x))]

indent :: Int -> String
indent n = '\n' : replicate (2*n) ' '

unlayout :: [Token] -> Option -> Colored String
unlayout ts o = unlayout' False (-1) ts where
  unlayout' needsSpace depth ts = case ts of
    []      -> Nil
    Layout t : ts
      | t == '{' -> (if depth == -1 then Nil else Value (indent (depth + 1))) <> unlayout' False (depth + 1) ts
      | t == ';' -> (if depth == 0 then Value "\n" else Nil) <> Value (indent depth) <> unlayout' False depth ts
      | t == '}' -> unlayout' False (depth - 1) ts
    t : ts -> let p = runPrintable (pretty t) o in if null p then unlayout' needsSpace depth ts else (if needsSpace then Value " " else Nil) <> p <> unlayout' True depth ts

instance (Term a, x ~ Annotation a) => Pretty (Tag (Source, Maybe x) a) where
  pretty x = Printable (unlayout (force unparse x))

label :: Term a => I a -> Maybe (Annotation a) -> Printable String
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
