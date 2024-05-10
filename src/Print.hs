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
    g x = Just $ Annotation (label x) : force f (view value x)

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
    Pair _ _       -> True
    Apply _ _      -> True
    Closure _ _    -> True
    Lambda _ _     -> True
    Read _ _       -> True
    Specialise _ _ -> True
    Sig _ _        -> True
    _              -> False
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
    IExp             -> prettyIf Types a
    IPat             -> prettyIf Types a
    IDataCon         -> prettyIf Types a
    ITyPat           -> prettyIf Kinds a
    IType            -> prettyIf Kinds a
    ITyRequirement   -> pretty a
    IKindRequirement -> pretty a
    _                -> blank
  _ -> blank

instance Pretty TyReason where
  pretty = \case
    TyReasonApply f x        -> "application " <> pretty f <> pretty (Fg Red (" ($) " :: Colored String)) <> pretty x
    TyReasonRead n           -> "read of " <> pretty n
    TyReasonBind p e         -> "binding " <> pretty p <> pretty (Fg Red (" (<-) " :: Colored String)) <> pretty e
    TyReasonIntegerLiteral i -> "integer literal " <> pretty (show i)
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
    KindReasonTyApply f x -> "type application " <> pretty f <> pretty (Fg Red (" ($) " :: Colored String)) <> pretty x
    KindReasonDataCon c   -> "data constructor " <> pretty c
    KindReasonData n a    -> "data type " <> pretty n <> (case a of { Just a -> " " <> pretty a; _ -> blank })
    KindReasonType t      -> "type " <> pretty t
