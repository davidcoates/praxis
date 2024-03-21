{-# LANGUAGE QuasiQuotes   #-}
{-# LANGUAGE TypeOperators #-}

module Translate
  ( runProgram
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term
import           Text.RawString.QQ


data Token = LBrace | RBrace | Semi | Token String | Crumb Source

ty :: (Term a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
ty = annotation . just

indent :: Int -> String
indent n = replicate (2*n) ' '

layout :: [Token] -> String
layout = layout' 0 "" where

  layout' :: Int -> String -> [Token] -> String
  layout' depth prefix ts = case ts of

    LBrace : ts -> "\n" ++ indent depth ++ "{" ++ layout' (depth + 1) ("\n" ++ indent (depth + 1)) ts

    RBrace : ts -> "\n" ++ indent (depth - 1) ++ "}" ++ layout' (depth - 1) ("\n" ++ indent (depth - 1)) ts

    Semi : ts -> ";" ++ layout' depth ("\n" ++ indent depth) ts

    Token t : ts -> prefix ++ t ++ layout' depth " " ts

    Crumb src : ts -> prefix ++ "/* " ++ show src ++ " */" ++ layout' depth " " ts

    [] -> ""


runProgram :: Annotated Program -> Praxis String
runProgram program = save stage $ do
  stage .= Translate
  return $ prelude ++ layout (translateProgram program)


translateProgram :: Annotated Program -> [Token]
translateProgram (_ :< Program decls) = concatMap translateDecl decls


translateQTyVar :: Annotated QTyVar -> [Token]
translateQTyVar (_ :< q) = case q of

  QTyVar n     -> [ Token "typename", Token n ]

  QViewVar _ n -> [ Token "typename", Token n ]


-- TODO... we need to know how QTypes are specialised

translateType :: Annotated Type -> [Token]
translateType (_ :< t) = case t of

  TyApply t1 t2
    | (_ :< View _) <- t1 -> translateType t2

  TyApply (_ :< TyCon n) t2 ->  [ Token n, Token "<" ] ++ intercalate [Token ","] (map translateType (unpack t2)) ++ [ Token ">" ] where
    unpack :: Annotated Type -> [Annotated Type]
    unpack t@(_ :< TyPack t1 t2) = t1 : unpack t2
    unpack t                     = [t]

  TyApply t1 t2 -> translateType t1 ++ [ Token "<" ] ++ translateType t2 ++ [ Token ">" ]

  TyCon n -> [ Token n ]

  TyFun t1 t2 -> [ Token "std::function<" ] ++ translateType t2 ++ [ Token "(" ] ++ translateType t1 ++ [ Token ")>" ]

  TyPair t1 t2 -> [ Token "std::pair<" ] ++ translateType t1 ++ [ Token "," ] ++ translateType t2 ++ [ Token ">" ]

  TyUnit -> [ Token "Unit" ]

  TyVar n -> [ Token n ]


translateQType :: Annotated QType -> [Token]
translateQType ((src, _) :< Forall vs _ t)
  | [] <- vs = translateType t
  | otherwise = [ Token "template<" ] ++ intercalate [Token ","] (map translateQTyVar vs) ++ [ Token ">" ] ++ translateType t


translateDecl :: Annotated Decl -> [Token]
translateDecl ((src, _) :< decl) = case decl of

  DeclRec decls -> concatMap translateForwardDecl decls ++ concatMap translateDecl decls

  DeclTerm name sig exp -> [ Crumb src ] ++ translateDeclTermType sig exp ++ [ Token name, Token "=" ] ++ translateExp exp ++ [ Semi ]

  where
    translateDeclTermType :: Maybe (Annotated QType) -> Annotated Exp -> [Token]
    translateDeclTermType sig exp
      | Just q <- sig = translateQType q
      | otherwise     = translateType (view ty exp)

    translateForwardDecl :: Annotated Decl -> [Token]
    translateForwardDecl ((src, _) :< DeclTerm name sig exp) = [ Crumb src ] ++ translateDeclTermType sig exp ++ [ Token name, Semi ]


translateExp :: Annotated Exp -> [Token]
translateExp exp = [ Token "(" ] ++ translateExp' exp ++ [ Token ")" ]

translateExp' :: Annotated Exp -> [Token]
translateExp' (_ :< exp) = case exp of

  Apply exp1 exp2 -> translateExp exp1 ++ [ Token "(" ] ++ translateExp exp2 ++ [ Token ")" ]

  Case exp alts -> undefined

  Cases alts -> undefined

  Con name -> [ Token name ] -- TODO need to qualify with type ?

  Defer exp1 exp2 -> [ LBrace, Token "auto ret ->" ] ++ translateExp exp1 ++ [ Semi ] ++ translateExp exp2 ++ [ Semi, Token "ret", Semi, RBrace ]

  If condExp thenExp elseExp -> translateExp condExp ++ [ Token "?" ] ++ translateExp thenExp ++ [ Token ":" ] ++ translateExp elseExp

  Lambda pat exp -> undefined

  Let bind exp -> undefined

  Lit lit -> undefined

  Read name exp -> undefined

  Pair exp1 exp2 -> [ Token "std::make_pair(" ] ++ translateExp exp1 ++ [Token ","] ++ translateExp exp2 ++ [Token ")"]

  Seq exp1 exp2 -> translateExp exp1 ++ [ Token "," ] ++ translateExp exp2

  Sig exp _ -> translateExp' exp

  Switch alts -> undefined

  Unit -> [ Token "Unit{}" ]

  Var name -> [ Token name ]

  Where exp decls -> [ LBrace ] ++ concatMap translateDecl decls ++ translateExp exp ++ [ Semi, RBrace ]


prelude :: String
prelude = [r|

struct Unit
{
};

|]
