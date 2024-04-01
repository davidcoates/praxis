{-# LANGUAGE QuasiQuotes   #-}
{-# LANGUAGE TypeOperators #-}

module Translate
  ( runProgram
  , prelude
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term
import           Text.RawString.QQ


data Token = LBrace | RBrace | Semi | Text String | Crumb Source

freshTempVar :: Praxis Name
freshTempVar = freshVar "_temp"

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

    Text t : ts -> prefix ++ t ++ layout' depth "" ts

    Crumb src : ts -> prefix ++ "/* " ++ show src ++ " */" ++ layout' depth ("\n" ++ indent depth) ts

    [] -> ""


runProgram :: Annotated Program -> Praxis String
runProgram program = save stage $ do
  stage .= Translate
  program <- layout <$> translateProgram program
  display program `ifFlag` debug
  return program


translateProgram :: Annotated Program -> Praxis [Token]
translateProgram (_ :< Program decls) = foldMapA (translateDecl True) decls


translateQTyVar :: Annotated QTyVar -> Praxis [Token]
translateQTyVar (_ :< q) = case q of

  QTyVar n     -> return [ Text "typename", Text n ]

  QViewVar _ n -> return [ Text "typename", Text n ]


-- TODO... we need to know how QTypes are specialised

translateType :: Annotated Type -> Praxis [Token]
translateType (_ :< t) = case t of

  TyApply t1 t2
    | (_ :< View _) <- t1 -> translateType t2

  TyApply (_ :< TyCon n) t2 -> do
    args <- intercalate [Text ", "] <$> mapM translateType (unpack t2)
    return $ [ Text n, Text "<" ] ++ args ++ [ Text ">" ]
    where
      unpack :: Annotated Type -> [Annotated Type]
      unpack t@(_ :< TyPack t1 t2) = t1 : unpack t2
      unpack t                     = [t]

  TyApply t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ t1 ++ [ Text "<" ] ++ t2 ++ [ Text ">" ]

  TyCon n -> return [ Text (translateName n) ] where
    translateName n = case n of
      "Int"    -> "int"
      "Array"  -> "std::vector"
      "Char"   -> "char"
      "Bool"   -> "bool"
      "String" -> "std::string"
      _        -> n

  TyFun t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ [ Text "std::function<" ] ++ t2 ++ [ Text "(" ] ++ t1 ++ [ Text ")>" ]

  TyPair t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ [ Text "std::pair<" ] ++ t1 ++ [ Text ", " ] ++ t2 ++ [ Text ">" ]

  TyUnit -> return [ Text "Unit" ]

  TyVar n -> return [ Text n ]


translateQType :: Annotated QType -> Praxis [Token]
translateQType ((src, _) :< Forall vs _ t)
  | [] <- vs = translateType t
  | otherwise = do
    vs <- mapM translateQTyVar vs
    t <- translateType t
    return $ [ Text "template<" ] ++ intercalate [ Text ", " ] vs ++ [ Text ">" ] ++ t


translateDecl :: Bool -> Annotated Decl -> Praxis [Token]
translateDecl topLevel ((src, _) :< decl) = case decl of

  DeclRec decls -> do
    forwardDecls <- foldMapA translateForwardDecl decls
    defns <- foldMapA (translateDecl topLevel) decls
    return $ forwardDecls ++ defns

  DeclTerm name sig exp -> do
    ty <- translateDeclTermType sig exp
    exp <- translateExp topLevel exp
    return $ [ Crumb src ] ++ ty ++ [ Text " ", Text name, Text " = " ] ++ exp ++ [ Semi ]

  where
    translateDeclTermType :: Maybe (Annotated QType) -> Annotated Exp -> Praxis [Token]
    translateDeclTermType sig exp
      | Just q <- sig = translateQType q
      | otherwise     = translateType (view ty exp)

    translateForwardDecl :: Annotated Decl -> Praxis [Token]
    translateForwardDecl ((src, _) :< DeclTerm name sig exp) = do
      ty <- translateDeclTermType sig exp
      return $ [ Crumb src ] ++ ty ++ [ Text " ", Text name, Semi ]


translateLit :: Lit -> Praxis [Token]
translateLit lit = return [ Text (translateLit' lit) ] where
  translateLit' lit = case lit of
    Bool bool     -> if bool then "true" else "false"
    Char char     -> show char
    Int int       -> show int
    String string -> show string

captureList :: Bool -> [Token]
captureList nonLocal = [ Text (if nonLocal then "[]" else "[=]") ]

lambdaWrap :: Bool -> [Token] -> [Token]
lambdaWrap nonLocal body = captureList nonLocal ++ [ Text "()", LBrace ] ++ body ++ [ RBrace, Text "()" ]

translateExp :: Bool -> Annotated Exp -> Praxis [Token]
translateExp nonLocal (_ :< exp) = case exp of

  Apply exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ exp1 ++ [ Text "(" ] ++ exp2 ++ [ Text ")" ]

  -- TODO
  Case exp alts -> undefined

  -- TODO
  Cases alts -> undefined

  Con name -> return [ Text name ] -- TODO need to qualify with type ?

  Defer exp1 exp2 -> do
    tempVar <- freshTempVar
    exp1 <- translateExp False exp1
    exp2 <- translateExp False exp2
    return $ lambdaWrap nonLocal ([ Text "auto ", Text tempVar, Text " = " ] ++ exp1 ++ [ Semi ] ++ exp2 ++ [ Semi, Text "return ", Text tempVar, Semi])

  If condExp thenExp elseExp -> do
    condExp <- translateExp nonLocal condExp
    thenExp <- translateExp nonLocal thenExp
    elseExp <- translateExp nonLocal elseExp
    return $ [ Text "(" ] ++ condExp ++ [ Text ") ? (" ] ++ thenExp ++ [ Text ") : (" ] ++ elseExp ++ [ Text ")" ]

  -- TODO
  Lambda pat exp -> do
    expTy <- translateType (view ty exp)
    tempVar <- freshTempVar
    body <- translateForceMatch tempVar pat exp
    return $ captureList nonLocal ++ [ Text "(" ] ++ expTy ++ [ Text " ", Text tempVar, Text ")", LBrace ] ++ body ++ [ RBrace ]

  Let (_ :< Bind pat exp1) exp2 -> do
    tempVar <- freshTempVar
    exp1 <- translateExp False exp1
    forceMatch <- translateForceMatch tempVar pat exp2
    return $ lambdaWrap nonLocal ([ Text "auto ", Text tempVar, Text " = " ] ++ exp1 ++ [ Semi ] ++ forceMatch)

  Lit lit -> translateLit lit

  Read _ exp -> translateExp nonLocal exp

  Pair exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ [ Text "std::make_pair(" ] ++ exp1 ++ [ Text ", " ] ++ exp2 ++ [ Text ")" ]

  Seq exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ [ Text "(" ] ++ exp1 ++ [ Text ", " ] ++ exp2 ++ [ Text ")" ]

  Sig exp _ -> translateExp nonLocal exp

  -- TODO
  Switch alts -> undefined

  Unit -> return [ Text "Unit{}" ]

  Var var -> return [ Text ("std::move(" ++ var ++ ")") ]

  Where exp decls -> do
    decls <- foldMapA (translateDecl False) decls
    exp <- translateExp False exp
    return $ lambdaWrap nonLocal (decls ++ [ Text "return " ] ++ exp ++ [ Semi ])


translateForceMatch :: Name -> Annotated Pat -> Annotated Exp -> Praxis [Token]
translateForceMatch var pat exp = do
  let src = view source pat
  exp <- translateExp False exp
  pat <- translateTryMatch var pat ([ Text "return " ] ++ exp ++ [ Semi ])
  return $ pat ++ [ Text ("throw MatchFail(\"" ++ show src ++ "\")"), Semi ]


translateTryMatch :: Name -> Annotated Pat -> [Token] -> Praxis [Token]
translateTryMatch var ((_, Just patTy) :< pat) onMatch = case pat of

  PatAt var' pat -> do
    pat <- translateTryMatch var' pat onMatch
    return $ [ Text "auto ", Text var', Text " = ", Text ("std::move(" ++ var ++ ")"), Semi ] ++ pat

  PatCon con pat -> do
    conType <- translateType patTy
    let tag = conType ++ [ Text ("::_TAG::" ++ con) ]
    tempVar <- freshTempVar
    case pat of
      Just pat -> do
        onMatch <- translateTryMatch tempVar pat onMatch
        return $ [ Text "if (", Text (var ++ "._tag"), Text " == " ] ++ tag ++ [ Text ")", LBrace, Text "auto ", Text tempVar, Text " = ", Text (var ++ "._get<") ] ++ tag ++ [ Text ">()", Semi ] ++ onMatch ++ [ RBrace ]
      Nothing -> return $ [ Text "if (", Text (var ++ "._tag"), Text " == " ] ++ tag ++ [ Text ")", LBrace ] ++ onMatch ++ [ RBrace ]

  PatHole -> return onMatch

  PatLit lit -> do
    lit <- translateLit lit
    return $ [ Text "if (", Text var, Text " == " ] ++ lit ++ [ Text ")", LBrace ] ++ onMatch ++ [ RBrace ]

  PatPair pat1 pat2 -> do
    var1 <- freshTempVar
    var2 <- freshTempVar
    pat2 <- translateTryMatch var2 pat2 onMatch
    onMatch <- translateTryMatch var1 pat1 pat2
    return $
      [ Text var1, Text " = ", Text (var ++ ".first"), Semi ] ++
      [ Text var2, Text " = ", Text (var ++ ".second"), Semi ] ++
      onMatch

  PatUnit -> return onMatch

  PatVar var' -> return $ [ Text "auto ", Text var', Text " = ", Text ("std::move(" ++ var ++ ")"), Semi ] ++ onMatch


prelude :: String
prelude = [r|/* prelude */
#include <utility>
#include <vector>
#include <string>
#include <stdexcept>
#include <algorithm>
#include <optional>

struct Unit
{
};

struct MatchFail : public std::runtime_error
{
  using std::runtime_error::runtime_error;
};

std::function<int(std::pair<int, int>)> add_int = [](auto p) { return p.first + p.second; };

/* prelude end */
|]
