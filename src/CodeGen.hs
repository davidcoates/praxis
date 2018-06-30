module CodeGen
  ( codeGen
  ) where

import           AST
import           Data.List (intercalate)
import           Inbuilts
import           Source
import           Tag
import           Type

codeGen :: Tagged (Type, Source) Exp -> String
codeGen = undefined

{-
codeGen :: Exp (Type, Pos) -> String
codeGen x = intercalate "\n" (map (defn . snd) inbuilts) ++ "\n\n" ++ cg x ++ "\n"

cg :: Exp (Type, Pos) -> String
cg (If _ a b c)         = cg a ++ " ? " ++ cg b ++ " : " ++ cg c
cg (Lit _ (Bool True))  = "true"
cg (Lit _ (Bool False)) = "false"
cg (Lit _ (Integer i))  = show i
cg (Var _ x)            = case lookup x inbuilts of Just td -> name td
cg (Apply _ a b)        = cg a ++ "(" ++ cg b ++ ")"
-}
