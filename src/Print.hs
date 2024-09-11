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
import           Term                 hiding (Value)
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
    Closure _ _    -> True
    Lambda _ _     -> True
    Read _ _       -> True
    Specialise _ _ -> True
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
    ITypeVar         -> prettypeIf Kinds a
    IType            -> prettypeIf Kinds a
    ITypeRequirement -> pretty a
    IKindRequirement -> pretty a
    _                -> blank
  _ -> blank

instance Pretty TypeReason where
  pretty = \case
    TypeReasonApply f x        -> "application " <> pretty f <> pretty (Colored.Fg Red (" ($) " :: Colored String)) <> pretty x
    TypeReasonRead n           -> "read of " <> pretty n
    TypeReasonBind p e         -> "binding " <> pretty p <> pretty (Colored.Fg Red (" (<-) " :: Colored String)) <> pretty e
    TypeReasonIntegerLiteral i -> "integer literal " <> pretty (show i)
    -- TODO
    Captured n       -> "variable " <> quote (pretty n) <> " captured"
    CaseCongruence   -> "alternatives of case expression must have the same type"
    ConPattern n     -> "constructor pattern " <> quote (pretty n)
    FnCongruence n  -> "function " <> quote (pretty n)
    FnSignature n   -> "function signature for " <> quote (pretty n)
    IfCondition      -> "type of if condition must be Bool"
    IfCongruence     -> "branches of if expression must have the same type"
    InstanceOf n     -> "monomorphic usage of " <> quote (pretty n)
    MultiAlias n     -> "variable " <> quote (pretty n) <> " is not a unique alias"
    MultiUse n       -> "variable " <> quote (pretty n) <> " used more than once"
    Specialisation n -> "specialisation of " <> quote (pretty n)
    SwitchCondition  -> "type of switch condition must be Bool"
    SwitchCongruence -> "branches of switch expression must have the same type"
    UserSignature    -> "user-supplied signature"

instance Pretty KindReason where
  pretty = \case
    KindReasonTypeApply f x   -> "type application " <> pretty f <> pretty (Colored.Fg Red (" $ " :: Colored String)) <> pretty x
    KindReasonTypeApplyOp f x -> "type operator application " <> pretty f <> pretty (Colored.Fg Red (" ★ " :: Colored String)) <> pretty x
    KindReasonDataCon c     -> "data constructor " <> pretty c
    KindReasonData n args   -> "data type " <> pretty n <> (case args of { [] -> ""; _ -> " with argument(s) " <> separate ", " args })
    KindReasonType t        -> "type " <> pretty t
    KindReasonTypeVar t       -> "type pattern " <> pretty t
    KindReasonQType t       -> "qualified type " <> pretty t
