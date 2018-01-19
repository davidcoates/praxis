module CodeGen
  ( codeGen
  ) where

import AST
import Type
import Inbuilts
import Data.List (intercalate)

codeGen :: Annotate (Type, SourcePos) Exp -> String
codeGen x = intercalate "\n" (map (defn . snd) inbuilts) ++ "\n\n" ++ cg x ++ "\n"

cg :: Annotate (Type, SourcePos) Exp -> String
cg (p :< e) = cg' e
  where cg' (If a b c) = cg a ++ " ? " ++ cg b ++ " : " ++ cg c
        cg' (Lit (Bool True))  = "true"
        cg' (Lit (Bool False)) = "false"
        cg' (Lit (Integer i))  = show i
        cg' (Var x) = case lookup x inbuilts of Just td -> name td
        cg' (Apply a b) = cg a ++ "(" ++ cg b ++ ")"
