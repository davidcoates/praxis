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
import           Data.Foldable        (toList)
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
      _         -> Print (Printable $ \o -> let l = runPrintable (label x) o in if null l then Nil else "[" <> l <> "]") : body
      where
        body = force f (view value x)
        prop = [Print ("[" <> pretty (show (view source x)) <> "]")] ++ [Print (Printable (layout body) <> "\n|-> " <> label x)]

indent :: Int -> String
indent n = replicate (2*n) ' '

layout :: [Token] -> Option -> Colored String
layout ts o = layout' (-1) Nil ts where

  layout' :: Int -> Colored String -> [Token] -> Colored String
  layout' depth prefix ts = case ts of

    Layout t : ts ->
      let
        depth' = case t of { '{' -> depth + 1 ; ';' -> depth ; '}' -> depth - 1 }
      in
        -- Note: Here we suppress newline for the top-level block start (the first token for programs)
        layout' depth' ((if depth == (-1) then "" else "\n") <> Value (indent depth')) ts

    t : ts ->
      let
        cs = runPrintable (pretty t) o
      in
        if null cs
          then layout' depth prefix ts
          else prefix <> cs <> layout' depth (Value " ") ts

    [] -> Nil


instance (Term a, x ~ Annotation a) => Pretty (Tag (Source, Maybe x) a) where
  pretty x = Printable (layout (force unparse x))

-- Do not show the label for compositional structures where the label of the parent is obvious from the label of the children.
-- I.e. ([a] a, ([b] b, [c] c)) instead of [(a, b, c)] ([a] a, [(b, c)] ([b] b, [c] c))
hideLabel :: Term a => a -> Bool
hideLabel x = case typeof x of
  IExp -> case x of
    Pair _ _   -> True
    Apply _ _  -> True
    Lambda _ _ -> True
    _          -> False
  IPat -> case x of
    PatPair _ _ -> True -- Note: Not trivial due to views: e.g. [?v (a, b)] (a, b) ~ ([?v a] a, ([?v b] b), but still simple enough to ignore.
    _           -> False
  ITyPat -> case x of
    TyPatPack _ _ -> True
    _             -> False
  IType -> case x of
    TyApply _ _ -> True
    TyPack _ _  -> True
    _           -> False
  IKind -> case x of
    KindPair _ _ -> True
    _            -> False
  _ -> False

label :: Term a => Annotated a -> Printable String
label ((s, a) :< x) = case a of
  Just a | not (hideLabel x) -> case typeof x of
    IExp      -> prettyIf Types a
    IPat      -> prettyIf Types a
    ITyPat    -> prettyIf Kinds a
    IType     -> prettyIf Kinds a
    ITyProp   -> pretty a
    IKindProp -> pretty a
    IDataCon  -> pretty a
    _         -> blank
  _ -> blank
