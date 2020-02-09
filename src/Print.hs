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
  annotated f = Printer $ \x -> let
    body  = force f (view value x)
    constraint = display (view source x) (\s -> "[" <> pretty s <> "]") ++ body ++ display (label (typeof x) (view annotation x)) id
    display s f = if s == mempty then [] else [Print (f s)]
      in Just $ case typeof x of
    ITypeConstraint -> constraint
    IKindConstraint -> constraint
    _               -> display (label (typeof x) (view annotation x)) (\l -> "[" <> pretty l <> "]") ++ body

indent :: Int -> Colored String
indent n
  | n <= 0    = "\n" -- TODO why are we getting -1?
  | otherwise = indent (n-1) <> "    "

unlayout :: [Token] -> Colored String
unlayout ts = unlayout' (-1) ts where
  unlayout' n ts = case ts of
    []      -> ""
    Special t : ts
      | t == '{' -> (if n >= 0 then indent (n+1) else Nil) <> unlayout' (n+1) ts
      | t == ';' -> indent n <> unlayout' n ts
      | t == '}' -> unlayout' (n-1) ts
    [t]    -> pretty t
    t : ts -> pretty t <> " " <> unlayout' n ts

instance (Recursive a, x ~ Annotation a) => Pretty (Tag (Source, Maybe x) a) where
  pretty = unlayout . force unparse

label :: Recursive a => I a -> Maybe (Annotation a) -> Colored String
label i Nothing  = Nil
label i (Just a) = case i of
  IExp            -> pretty a
  IPat            -> pretty a
  ITyPat          -> pretty a
  IType           -> pretty a
  ITypeConstraint -> pretty a
  IKindConstraint -> pretty a
  IDataAlt        -> pretty a
  _               -> Nil
