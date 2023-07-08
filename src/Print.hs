{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Print
  (
  ) where

import           Common
import qualified Data.Monoid.Colorful as Colorful
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
      ITyProp   -> prop
      IKindProp -> prop
      i         -> [Print (mapIfNotNull (\c -> "[" <> c <> "]") (label i (view annotation x)))] ++ body
      where
        body = force f (view value x)
        prop = (if view source x == Phantom then [] else [Print ("[" <> pretty (show (view source x)) <> "]")]) ++ body ++ [Print (label (typeof (view value x)) (view annotation x))]

indent :: Int -> String
indent n = replicate (2*n) ' '

layout :: [Token] -> Option -> Colored String
layout ts o = foldLines (layout' False (-1) ts Nil) where

  foldLines :: [Colored String] -> Colored String
  foldLines ls = fold . intersperse (Value "\n") $ concatMap (\cs -> [cs | not (null cs)]) ls where

  layout' :: Bool -> Int -> [Token] -> Colored String -> [Colored String]
  layout' needsSpace depth ts line = case ts of

    []      -> [line]

    Layout t : ts
      | t == '{' -> line : layout' False (depth + 1) ts (Value (indent (depth + 1)))
      | t == ';' -> line : layout' False depth ts (Value (indent depth))
      | t == '}' -> layout' False (depth - 1) ts line

    t : ts -> let cs = runPrintable (pretty t) o in
      if null cs
      then layout' needsSpace depth ts line
      else layout' True depth ts (line <> (if needsSpace then Value " " else Nil) <> cs)


instance (Term a, x ~ Annotation a) => Pretty (Tag (Source, Maybe x) a) where
  pretty x = Printable (layout (force unparse x))

label :: Term a => I a -> Maybe (Annotation a) -> Printable String
label _ Nothing  = blank
label i (Just a) = case i of
  IExp      -> prettyIf Types a
  IPat      -> prettyIf Types a
  ITyPat    -> prettyIf Kinds a
  IType     -> prettyIf Kinds a
  ITyProp   -> pretty a
  IKindProp -> pretty a
  IDataCon  -> pretty a
  _         -> blank
