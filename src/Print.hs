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
import qualified Data.Monoid.Colorful as Colored
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
  expected s = Printer (error s)
  annotated (Printer f) = Printer $ \x -> case f (view value x) of
    Nothing -> Nothing
    Just xs -> Just $ Annotation (label x) : xs

indent :: Int -> String
indent n = replicate (2*n) ' '

layout :: [Token] -> Option -> Colored String
layout ts o = layout' (-1) Colored.Nil ts where

  layout' :: Int -> Colored String -> [Token] -> Colored String
  layout' depth prefix ts = case ts of

    Layout t : ts ->
      let
        depth' = case t of { '{' -> depth + 1 ; ';' -> depth ; '}' -> depth - 1 }
      in
        -- Note: Here we suppress newline for the top-level block start (the first token for programs)
        layout' depth' ((if depth == (-1) then "" else "\n") <> Colored.Value (indent depth')) ts

    t : ts ->
      let
        cs = runPrintable (pretty t) o
      in
        if null cs
          then layout' depth prefix ts
          else prefix <> cs <> layout' depth (Colored.Value " ") ts

    [] -> Colored.Nil


instance (Term a, x ~ Annotation a) => Pretty (Tag (Source, Maybe x) a) where
  pretty x = Printable (layout (force unparse x))

-- Do not show the label for compositional structures where the label of the parent is obvious from the label of the children.
-- I.e. ([a] a, ([b] b, [c] c)) instead of [(a, b, c)] ([a] a, [(b, c)] ([b] b, [c] c))
hideLabel :: Term a => a -> Bool
hideLabel x = case typeof x of
  IExp -> case x of
    Pair _ _       -> True
    Apply _ _      -> True
    Capture _ _    -> True
    Lambda _ _     -> True
    Read _ _       -> True
    Specialize _ _ -> True
    Sig _ _        -> True
    _              -> False
  IPat -> case x of
    PatPair _ _ -> True -- Note: Not trivial due to references/views: e.g. [?v (a, b)] (a, b) ~ ([?v a] a, ([?v b] b), but still simple enough to ignore.
    _           -> False
  IType -> case x of
    TypeApply _ _   -> True
    TypeApplyOp _ _ -> True
    _               -> False
  _ -> False

label :: Term a => Annotated a -> Printable String
label ((s, a) :< x) = case a of
  Just a | not (hideLabel x) -> case typeof x of
    IExp             -> prettypeIf Types a
    IPat             -> prettypeIf Types a
    IDataCon         -> prettypeIf Types a
    ITypePat         -> prettypeIf Kinds a
    IType            -> prettypeIf Kinds a
    ITypeRequirement -> pretty a
    IKindRequirement -> pretty a
    _                -> blank
  _ -> blank

instance Pretty TypeReason where
  pretty = \case
    TypeReasonApply f x -> "application " <> pretty f <> pretty (Colored.Fg Red (" ($) " :: Colored String)) <> pretty x
    TypeReasonBind p e -> "binding " <> pretty p <> pretty (Colored.Fg Red (" (<-) " :: Colored String)) <> pretty e
    TypeReasonCaptured n -> "variable " <> pretty n <> " captured"
    TypeReasonCaseCongruence -> "case(s) expression branches must have the same type"
    TypeReasonConstructor n  -> "constructor " <> pretty n
    TypeReasonFunctionCongruence n sig -> case sig of
      Nothing  -> "function " <> pretty n
      Just sig -> "function " <> pretty n <> " with signature " <> pretty sig
    TypeReasonIfCondition  -> "if expression condition must have type Bool"
    TypeReasonIfCongruence -> "if expression branches must have the same type"
    TypeReasonIntegerLiteral i -> "integer literal " <> pretty (show i)
    TypeReasonRead n -> "read of " <> pretty n
    TypeReasonSignature t -> "signature " <> pretty t
    TypeReasonSpecialization n -> "specialization of " <> pretty n
    TypeReasonSwitchCondition -> "switch expression condition must have type Bool"
    TypeReasonSwitchCongruence -> "switch expression branches must have the same type"
    TypeReasonMultiAlias n -> "variable " <> pretty n <> " is not a unique alias"
    TypeReasonMultiUse n -> "variable " <> pretty n <> " used more than once"

instance Pretty KindReason where
  pretty = \case
    KindReasonTypeApply f x -> "type application " <> pretty f <> pretty (Colored.Fg Red (" ($) " :: Colored String)) <> pretty x
    KindReasonTypeApplyOp f x -> "type operator application " <> pretty f <> pretty (Colored.Fg Red (" (★) " :: Colored String)) <> pretty x
    KindReasonDataCon c -> "data constructor " <> pretty c
    KindReasonData n args -> "data type " <> pretty n <> (case args of { [] -> ""; _ -> " with argument(s) " <> separate ", " args })
    KindReasonType t -> "type " <> pretty t
    KindReasonTypePat t -> "type pattern " <> pretty t
    KindReasonQType t -> "qualified type " <> pretty t
