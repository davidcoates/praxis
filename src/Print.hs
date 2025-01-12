{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE InstanceSigs          #-}

module Print
  (
  ) where

import           Common
import           Data.Foldable        (toList)
import qualified Data.Monoid.Colorful as Colored
import           Introspect
import           Stage
import           Syntax.Prism
import qualified Syntax.Syntax        as Syntax
import           Syntax.Syntax        (Syntax)
import           Syntax.Term
import           Term
import           Token


newtype Printer a = Printer { runPrinter :: a -> Maybe [Token] }

force :: Printer a -> a -> [Token]
force (Printer f) x = case f x of
  Nothing -> []
  Just xs -> xs

instance Syntax Printer where
  f <$> g = Printer $ \x -> case destruct f x of
    Nothing -> Nothing
    Just y  -> Just (force g y)
  f <*> g = Printer $ \(a, b) -> Just (force f a ++ force g b)
  empty = Printer $ const Nothing
  Printer f <|> Printer g = Printer $ \x -> case f x of
    Nothing -> g x
    Just xs -> Just xs
  pure = const Syntax.empty
  match _ f = Printer $ \x -> Just [f x]
  expected err = Printer (error err)
  annotated (Printer f) = Printer $ \x -> case f (view value x) of
    Nothing -> Nothing
    Just xs -> Just (Annotation (label x) : xs)
  internal = id

  rightWithSep :: forall a s. (IsTerm a, IsStage s) => Printer () -> Prism (a s) (Annotated s a, Annotated s a) -> Printer (a s) -> Printer (a s)
  rightWithSep s _P p = Printer unfold Syntax.<|> p where
    unfold x = case destruct _P x of
      Just (a1 :< x1, a2 :< x2) -> Just $ (Annotation (label (a1 :< x1)) : force p x1) ++ force s () ++ (Annotation (label (a2 :< x2)) : force (Syntax.rightWithSep s _P p) x2)
      Nothing -> Nothing

  leftWithSep :: forall a s. (IsTerm a, IsStage s) => Printer () -> Prism (a s) (Annotated s a, Annotated s a) -> Printer (a s) -> Printer (a s)
  leftWithSep s _P p = Printer unfold Syntax.<|> p where
    unfold x = case destruct _P x of
      Just (a1 :< x1, a2 :< x2) -> Just $ (Annotation (label (a1 :< x1)) : force (Syntax.leftWithSep s _P p) x1) ++ force s () ++ (Annotation (label (a2 :< x2)) : force p x2)
      Nothing -> Nothing

  foldType :: forall s. (IsStage s) => Printer (Type s) -> Printer (Type s)
  foldType p = Printer (Just . unfold) where
    unfold :: Type s -> [Token]
    unfold x = case x of
      TypeApplyOp (a1 :< x1) (a2 :< x2) -> (Annotation (label (a1 :< x1)) : force p x1) ++ (Annotation (label (a2 :< x2)) : unfold x2)
      TypeApply _ _ -> unfoldLeft x
      _ -> force p x
    unfoldLeft :: Type s -> [Token]
    unfoldLeft x = case x of
      TypeApply (a1 :< x1) (a2 :< x2) -> (Annotation (label (a1 :< x1)) : unfoldLeft x1) ++ (Annotation (label (a2 :< x2)) : force p x2)
      _ -> force p x


indent :: Int -> String
indent n = replicate (2*n) ' '

layout :: [Token] -> Colored String
layout ts = layout' (-1) Colored.Nil ts where

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
        cs = pretty t
      in
        if null cs
          then layout' depth prefix ts
          else prefix <> cs <> layout' depth (Colored.Value " ") ts

    [] -> Colored.Nil


instance (IsTerm a, IsStage s, x ~ Annotation s a) => Pretty (Tag (Source, x) (a s)) where
  pretty x = layout (force (Syntax.annotated (syntax (termT :: TermT a))) x)

-- Do not show the label for compositional structures where the label of the parent is obvious from the label of the children.
-- I.e. ([a] a, ([b] b, [c] c)) instead of [(a, b, c)] ([a] a, [(b, c)] ([b] b, [c] c))
hideLabel :: IsTerm a => a s -> Bool
hideLabel x = case typeof x of
  ExpT -> case x of
    Pair _ _       -> True
    Apply _ _      -> True
    Capture _ _    -> True
    Lambda _ _     -> True
    Read _ _       -> True
    Specialize _ _ -> True
    Sig _ _        -> True
    _              -> False
  PatT -> case x of
    PatPair _ _ -> True -- Note: Not trivial due to references/views: e.g. [?v (a, b)] (a, b) ~ ([?v a] a, ([?v b] b), but still simple enough to ignore.
    _           -> False
  TypeT -> case x of
    TypeApply _ _   -> True
    TypeApplyOp _ _ -> True
    _               -> False
  _ -> False

label :: forall a s. (IsTerm a, IsStage s) => Annotated s a -> Colored String
label ((s, a) :< x)
  | hideLabel x = Colored.Nil
  | otherwise = let stage = (stageT :: StageT s) in case termT :: TermT a of
    ExpT
      | TypeCheckT <- stage -> pretty a
    DataConT
      | TypeCheckT <- stage -> pretty a
    KindRequirementT
      | KindCheckT <- stage -> pretty a
    PatT
      | TypeCheckT <- stage -> pretty a
    TypeT
      | KindCheckT <- stage -> pretty a
    TypePatT
      | KindCheckT <- stage -> pretty a
    TypeRequirementT
      | TypeCheckT <- stage -> pretty a
    _ -> Colored.Nil

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
