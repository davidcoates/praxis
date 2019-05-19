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
  annotated (Printer f) = Printer $ \(_ :< x) -> f x -- TODO
  mark s = Printer (error s)

unlayout :: [Token] -> String
unlayout ts = unlayout' (-1) ts where
  unlayout' n ts = case ts of
    []               -> ""
    Special '{' : ts -> (if n >= 0 then "\n" ++ replicate (n+1) '\t' else "") ++ unlayout' (n+1) ts
    Special ';' : ts -> "\n" ++ replicate n '\t' ++ unlayout' n ts
    Special '}' : ts -> unlayout' (n-1) ts
    t : ts           -> show t ++ " " ++ unlayout' n ts

instance (Complete s, Recursive a, x ~ Annotation s a) => Show (Tag (Source, x) (a s)) where
  show = unlayout . force unparse

{-
instance (Complete s, Recursive a, x ~ Annotation s a) => Show (Tag (Source, x) (a s)) where
  show t = case (witness :: I a) of
    ITypeConstraint -> proofShow t
    IKindConstraint -> proofShow t
    _               -> flatShow t
    where
    proofShow t@((s, a) :< x) = sourceShow s ++ show' x ++ anteShow (label t) where
      sourceShow Phantom = ""
      sourceShow s       = "[" ++ show (start s) ++ "] "
      anteShow l | l == "" = ""
      anteShow l = " " ++ l
    flatShow t@((s, a) :< x) = annShow s (label t) ++ show' x where
      annShow Phantom l | l == "" = ""
      annShow Phantom l = "[" ++ l ++ "] "
      annShow s       l | l == "" = "[" ++ show (start s) ++ "] "
      annShow s       l = "[" ++ l ++ " " ++ show (start s) ++ "] "
-}
