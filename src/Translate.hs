{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeOperators     #-}

module Translate
  ( runProgram
  , Mode(..)
  ) where

import           Common            hiding (Nil, intercalate)
import           Introspect
import           Praxis
import           Stage
import           Term

import           Data.FileEmbed    (embedStringFile)
import           Data.String       (IsString (..))
import           Prelude           hiding (concat)
import           Text.RawString.QQ


freshTempVar :: Praxis Name
freshTempVar = freshVar "_temp"

ty :: (Term a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
ty = annotation . just

data Code = Nil | Join Code Code | LBrace | RBrace | Semi | Newline | Crumb Source | Text String

instance IsString Code where
  fromString = Text

instance Semigroup Code where
  c1 <> c2 = Join c1 c2

instance Monoid Code where
  mempty = Nil

intercalate :: Code -> [Code] -> Code
intercalate   _     [] = Nil
intercalate   _    [c] = c
intercalate sep (c:cs) = Join c (Join sep (intercalate sep cs))

concat :: [Code] -> Code
concat []     = Nil
concat (c:cs) = Join c (concat cs)

layout :: Code -> String
layout code = layout' 0 "" (unroll code) where

  layout' :: Int -> String -> [Code] -> String
  layout' depth prefix cs = case cs of

    LBrace : cs -> "{" ++ layout' (depth + 1) ("\n" ++ indent (depth + 1)) cs

    RBrace : cs -> "\n" ++ indent (depth - 1) ++ "}" ++ layout' (depth - 1) "" cs

    Semi : cs -> ";" ++ layout' depth ("\n" ++ indent depth) cs

    Text t : cs -> prefix ++ t ++ layout' depth "" cs

    Crumb src : cs -> prefix ++ "/* " ++ show src ++ " */" ++ layout' depth ("\n" ++ indent depth) cs

    Newline : cs -> "\n" ++ layout' depth (indent depth) cs

    [] -> ""

  indent :: Int -> String
  indent n = replicate (2*n) ' '

  unroll :: Code -> [Code]
  unroll code = case code of
    Nil        -> []
    Join c1 c2 -> unroll c1 ++ unroll c2
    _          -> [code]


data Mode = NoPrelude | Prelude | PreludeWithMain

runProgram :: Mode -> Annotated Program -> Praxis String
runProgram mode program = save stage $ do
  stage .= Translate
  program <- layout <$> translateProgram program
  display program `ifFlag` debug
  let wrappedProgram = prelude ++ "namespace praxis::user {\n" ++ program ++ "\n}"
  case mode of
    NoPrelude       -> return program
    Prelude         -> return wrappedProgram
    PreludeWithMain -> requireMain >> return (wrappedProgram ++ "\nint main(){ praxis::user::main_0(std::monostate{}); }")


translateProgram :: Annotated Program -> Praxis Code
translateProgram (_ :< Program decls) = foldMapA (translateDecl True) decls

-- QViewVar's with a ref domain (e.g. &r) are not needed past the type checking stage. They are dropped from the translated code.
canTranslateQTyVar :: Annotated QTyVar -> Bool
canTranslateQTyVar qTyVar = case view value qTyVar of
  QViewVar Ref _ -> False
  _              -> True

translatableQTyVars :: [Annotated QTyVar] -> [Annotated QTyVar]
translatableQTyVars = filter canTranslateQTyVar

translateQTyVar :: Annotated QTyVar -> Praxis Code
translateQTyVar (_ :< q) = case q of

  QTyVar n              -> return $ "typename " <> Text n

  QViewVar RefOrValue n -> return $ "praxis::View " <> Text n


translateView :: Annotated View -> Praxis Code
translateView (_ :< v) = case v of

  ViewValue            -> return "praxis::View::VALUE"

  ViewRef _            -> return "praxis::View::REF"

  ViewVar Ref _        -> return "praxis::View::REF"

  ViewVar RefOrValue n -> return (Text n)


translateType :: Annotated Type -> Praxis Code
translateType (_ :< t) = case t of

  TyApply t1 t2
    | (_ :< TyView view) <- t1 -> do
      view <- translateView view
      t2 <- translateType t2
      return $ "praxis::apply<" <> view <> ", " <> t2 <> ">"

  TyApply (_ :< TyCon n) t2 -> do
    args <- (intercalate ", " <$>) (mapM translateType (unpack t2))
    return $ Text n <> "<" <> args <> ">"
    where
      unpack :: Annotated Type -> [Annotated Type]
      unpack t@(_ :< TyPack t1 t2) = t1 : unpack t2
      unpack t                     = [t]

  TyApply t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ t1 <> "<" <> t2 <> ">"

  TyCon n -> return $ Text n

  TyFun t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ "std::function<" <> t2 <> "(" <> t1 <> ")>"

  TyPair t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ "std::pair<" <> t1 <> ", " <> t2 <> ">"

  TyUnit -> return "std::monostate"

  TyVar n -> return (Text n)

  TyView v -> translateView v


translateQType :: Annotated QType -> Praxis Code
translateQType ((src, _) :< Forall vs _ t) = translateQType' (translatableQTyVars vs) where
  translateQType' vs
    | [] <- vs = translateType t
    | otherwise = do
      vs <- mapM translateQTyVar vs
      t <- translateType t
      return $ "template<" <> intercalate ", " vs <> ">" <> t


translateDeclType :: Annotated DeclType -> Praxis Code
translateDeclType (_ :< DeclTypeEnum name alts) = return $ "enum " <> Text name <> " " <> LBrace <> intercalate ", " [ "_con" <> Text alt | alt <- alts ] <> RBrace <> Semi
translateDeclType (_ :< DeclTypeData mode name tyPat alts) = do

  let tyPats = case tyPat of { Just tyPat -> unpackTyPat tyPat; Nothing -> []; }

  alts <- mapM (\(_ :< DataCon name ty) -> (name,) <$> translateType ty) alts

  let
    tyPatsDecl = case tyPats of
      [] -> Nil
      _  -> "template<" <> intercalate ", " (map tyPatDecl tyPats) <> ">" <> Newline

    fullTy = case tyPats of
      [] -> Text name
      _  -> Text name <> "<" <> intercalate ", " (map tyPatInst tyPats) <> ">"

    variantTy = "std::variant<" <> intercalate ", " (map snd alts) <> ">"

    body = "using " <> variantTy <> "::variant" <> Semi <> "template<size_t index>" <> Newline <> "inline const auto& get() const { return std::get<index>(*this); }" <> Newline <> "template<size_t index>" <> Newline <> "inline auto& get() { return std::get<index>(*this); }"

    defn = case mode of
      DataUnboxed
        -> tyPatsDecl <> "struct "      <> Text name <> " : " <> variantTy <> " " <> LBrace <> body <> RBrace <> Semi
      _
        -> tyPatsDecl <> "struct _impl" <> Text name <> Semi <> tyPatsDecl <> "using " <> Text name <> " = praxis::Boxed<_impl" <> fullTy <> ">" <> Semi <> -- forward declaration
           tyPatsDecl <> "struct _impl" <> Text name <> " : " <> variantTy <> " " <> LBrace <> body <> RBrace <> Semi


    altIndices = concat [ "static constexpr size_t _idx" <> Text name <> " = " <> Text (show i) <> Semi | (name, i) <- zip (map fst alts) [0..] ]

    altConstructors = concat [ altConstructor name ty | (name, ty) <- alts ] where

      constructor = case mode of
        DataUnboxed -> fullTy
        _           -> "praxis::mkBoxed<_impl"  <> fullTy <> ">"

      altConstructorBody :: Name -> Code -> Code
      altConstructorBody altName ty = "std::function([](" <> ty <> "&& arg) -> " <> fullTy <> " " <> LBrace <> "return " <> constructor <> "(std::in_place_index<_idx" <> Text altName <> ">, std::move(arg))" <> Semi <> RBrace <> ")" where

      altConstructor :: Name -> Code -> Code
      altConstructor altName ty = "auto _con" <> Text altName <> " = " <> case tyPats of
        [] -> altConstructorBody altName ty
        _  -> "[]<" <> intercalate ", " (map tyPatDecl tyPats) <> ">()" <> LBrace <> "return " <> altConstructorBody altName ty <> Semi <> RBrace <> Semi


  return $ defn <> altIndices <> altConstructors

  where
    tyPatDecl :: Annotated TyPat -> Code
    tyPatDecl tyPat = case view value tyPat of
      TyPatVar name                -> "typename " <> Text name
      TyPatViewVar RefOrValue name -> "praxis::View " <> Text name

    tyPatInst :: Annotated TyPat -> Code
    tyPatInst tyPat = case view value tyPat of
      TyPatVar name                -> Text name
      TyPatViewVar RefOrValue name -> Text name

    -- unpack to a list of TyPatVar and TyPatViewVar, skipping Ref domain TyPatViewVar
    unpackTyPat :: Annotated TyPat -> [Annotated TyPat]
    unpackTyPat tyPat = case view value tyPat of
      TyPatPack p1 p2           -> unpackTyPat p1 ++ unpackTyPat p2
      TyPatVar _                -> [tyPat]
      TyPatViewVar RefOrValue _ -> [tyPat]
      TyPatViewVar Ref _        -> []



translateDecl :: Bool -> Annotated Decl -> Praxis Code
translateDecl topLevel ((src, _) :< decl) = case decl of

  DeclRec decls -> do
    rec0 <- freshTempVar
    rec1 <- freshTempVar
    let unpack :: Name -> Code
        unpack rec = "auto [" <> intercalate ", " [ Text name | (_ :< DeclVar name _ _) <- decls ] <> "] = " <> Text rec <> "(" <> Text rec <> ")" <> Semi
    typeHint <- recTypeHint decls
    decls <- mapM (\(_ :< DeclVar _ sig exp) -> (Crumb src <>) <$> translateDeclVarBody sig (unpack rec1) False exp) decls
    return $ "auto " <> Text rec0 <> " = " <> captureList topLevel <> "(auto " <> Text rec1 <> ")" <> typeHint <> LBrace <> "return std::tuple" <> LBrace <> intercalate (Join "," Newline) decls <> RBrace <> Semi <> RBrace <> Semi <> unpack rec0

  DeclVar name sig exp -> do
    body <- translateDeclVarBody sig Nil topLevel exp
    return $ Crumb src <> "auto " <> Text name <> " = " <> body <> Semi

  DeclType ty -> translateDeclType ty

  where
    templateVars :: Maybe (Annotated QType) -> [Annotated QTyVar]
    templateVars sig = case sig of
      Nothing                   -> []
      Just (_ :< Forall vs _ _) -> translatableQTyVars vs

    isTemplated :: Maybe (Annotated QType) -> Bool
    isTemplated = not . null . templateVars

    translateDeclVarBody :: Maybe (Annotated QType) -> Code -> Bool -> Annotated Exp -> Praxis Code
    translateDeclVarBody sig recPrefix nonLocal exp = case templateVars sig of
      [] -> translateExp' recPrefix nonLocal exp
      vs -> do
        vs <- mapM translateQTyVar vs
        exp <- translateExp' recPrefix False exp
        return $ captureList nonLocal <> "<" <> intercalate ", " vs <> ">()" <> LBrace <> "return " <> exp <> Semi <> RBrace

    -- TODO auto deduction may not work if some decls are templated but some arent?
    recTypeHint :: [Annotated Decl] -> Praxis Code
    recTypeHint decls
      | all (\(_ :< DeclVar _ sig _) -> not (isTemplated sig)) decls
        = do
          -- all decls are non-templated
          tys <- mapM (\(_ :< DeclVar _ _ exp) -> translateType (view ty exp)) decls
          return $ " -> std::tuple<" <> intercalate ", " tys <> "> "
      | otherwise
        = return Nil


translateLit :: Annotated Type -> Lit -> Praxis Code
translateLit ty lit = case lit of
  Bool bool
    -> return (if bool then "true" else "false")
  Char char
    -> return (Text (show char))
  Integer int -> do
    ty <- translateType ty
    return $ "static_cast<" <> ty <> ">(" <> Text (show int) <> ")"
  String string
    -> return (Text (show string))

captureList :: Bool -> Code
captureList nonLocal = if nonLocal then "[]" else "[&]"

lambdaWrap :: Bool -> Code -> Code
lambdaWrap nonLocal body = captureList nonLocal <> "()" <> LBrace <> body <> RBrace <> "()"

translateExp :: Bool -> Annotated Exp -> Praxis Code
translateExp = translateExp' Nil

translateExp' :: Code -> Bool -> Annotated Exp -> Praxis Code
translateExp' recPrefix nonLocal ((src, Just expTy) :< exp) = case exp of

  Apply exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ exp1 <> "(" <> exp2 <> ")"

  Case exp alts -> do
    tempVar <- freshTempVar
    exp <- translateExp False exp
    alts <- translateCase src tempVar alts
    return $ lambdaWrap nonLocal ("auto " <> Text tempVar <> " = " <> exp <> Semi <> alts)

  Cases alts -> do
    tempVar <- freshTempVar
    let (_ :< TyFun tempVarTy _) = expTy
    tempVarTy <- translateType tempVarTy
    alts <- translateCase src tempVar alts
    return $ "std::function(" <> captureList nonLocal <> "(" <> tempVarTy <> " " <> Text tempVar <> ")" <> LBrace <> recPrefix <> alts <> RBrace <> ")"

  Con name -> return ("_con" <> Text name)

  Defer exp1 exp2 -> do
    tempVar <- freshTempVar
    exp1 <- translateExp False exp1
    exp2 <- translateExp False exp2
    return $ lambdaWrap nonLocal ("auto " <> Text tempVar <> " = " <> exp1 <> Semi <> exp2 <> Semi <> "return " <> Text tempVar <> Semi)

  If condExp thenExp elseExp -> do
    condExp <- translateExp nonLocal condExp
    thenExp <- translateExp nonLocal thenExp
    elseExp <- translateExp nonLocal elseExp
    return $ "(" <> condExp <> ") ? (" <> thenExp <> ") : (" <> elseExp <> ")"

  Lambda pat exp -> do
    patTy <- translateType (view ty pat)
    tempVar <- freshTempVar
    body <- translateBind tempVar pat exp
    return $ "std::function(" <> captureList nonLocal <> "(" <> patTy <> " " <> Text tempVar <> ")" <> LBrace <> recPrefix <> body <> RBrace <> ")"

  Let (_ :< Bind pat exp1) exp2 -> do
    tempVar <- freshTempVar
    exp1 <- translateExp False exp1
    bind <- translateBind tempVar pat exp2
    return $ lambdaWrap nonLocal ("auto " <> Text tempVar <> " = " <> exp1 <> Semi <> bind)

  Lit lit -> translateLit expTy lit

  Read name exp -> do
    tempVar <- freshTempVar
    exp <- translateExp False exp
    return $ lambdaWrap nonLocal ("const auto& " <> Text tempVar <> " = " <> Text name <> Semi <> "auto " <> Text name <> " = praxis::ref(" <> Text tempVar <> ")" <> Semi <> "return " <> exp <> Semi)

  Pair exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ "std::make_pair(" <> exp1 <> ", " <> exp2 <> ")"

  Seq exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ "(" <> exp1 <> ", " <> exp2 <> ")"

  Sig exp _ -> translateExp nonLocal exp

  Specialise exp specialisation -> do
    exp <- translateExp nonLocal exp
    let tyArgs = [ t | (qTyVar, t) <- specialisation, canTranslateQTyVar qTyVar ]
    tyArgs <- mapM translateType tyArgs
    return $ case tyArgs of
      [] -> exp
      _  -> exp <> ".template operator()<" <> intercalate ", " tyArgs <> ">()"

  Switch alts -> do
    alts <- translateSwitch src alts
    return $ lambdaWrap nonLocal alts

  Unit -> return "std::monostate{}"

  Var var -> return $ "std::move(" <> Text var <> ")"

  Where exp decls -> do
    decls <- foldMapA (translateDecl False) decls
    exp <- translateExp False exp
    return $ lambdaWrap nonLocal (decls <> "return " <> exp <> Semi)


translateSwitch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis Code
translateSwitch src [] = return $ "throw praxis::SwitchFail(\"" <> Text (show src) <> "\")" <> Semi
translateSwitch src ((cond, exp):alts) = do
  cond <- translateExp False cond
  exp <- translateExp False exp
  alts <- translateSwitch src alts
  return $ "if (" <> cond <> ") " <> LBrace <> "return " <> exp <> Semi <> RBrace <> Newline <> alts


translateCase :: Source -> Name -> [(Annotated Pat, Annotated Exp)] -> Praxis Code
translateCase src _ [] = return $ "throw praxis::CaseFail(\"" <> Text (show src) <> "\")" <> Semi
translateCase src var ((pat, exp):alts) =  do
  exp <- translateExp False exp
  onMatch <- translateTryMatch var pat ("return " <> exp <> Semi)
  onNoMatch <- translateCase src var alts
  return $ onMatch <> onNoMatch


translateBind :: Name -> Annotated Pat -> Annotated Exp -> Praxis Code
translateBind var pat exp = do
  let src = view source pat
  exp <- translateExp False exp
  pat <- translateTryMatch var pat ("return " <> exp <> Semi)
  return $ pat <> "throw praxis::BindFail(\"" <> Text (show src) <> "\")" <> Semi


translateTryMatch :: Name -> Annotated Pat -> Code -> Praxis Code
translateTryMatch var ((_, Just patTy) :< pat) onMatch = case pat of

  PatAt var' pat -> do
    pat <- translateTryMatch var' pat onMatch
    return $ "auto " <> Text var' <> " = std::move(" <> Text var <> ")" <> Semi <> pat

  PatData name pat -> do
    tempVar <- freshTempVar
    onMatch <- translateTryMatch tempVar pat onMatch
    return $ "if (" <> Text var <> ".index() == _idx" <> Text name <> ") " <> LBrace <> "auto " <> Text tempVar <>  " = " <> Text var <> ".template get<_idx" <> Text name <> ">()" <> Semi <> onMatch <> RBrace <> Newline

  PatEnum name -> do
    return $ "if (" <> Text var <> " == _con" <> Text name <> ") " <> LBrace <> onMatch <> RBrace <> Newline

  PatHole -> return onMatch

  PatLit lit -> do
    lit <- translateLit patTy lit
    return $ "if (" <> Text var <> " == " <> lit <> ") " <> LBrace <> onMatch <> RBrace <> Newline

  PatPair pat1 pat2 -> do
    var1 <- freshTempVar
    var2 <- freshTempVar
    pat2 <- translateTryMatch var2 pat2 onMatch
    onMatch <- translateTryMatch var1 pat1 pat2
    return $
      "auto " <> Text var1 <> " = praxis::first(" <> Text var <> ")" <> Semi <>
      "auto " <> Text var2 <> " = praxis::second(" <> Text var <> ")" <> Semi <>
      onMatch

  PatUnit -> return onMatch

  PatVar var' -> return $ "auto " <> Text var' <> " = std::move(" <> Text var <> ")" <> Semi <> onMatch

prelude :: String
prelude = $(embedStringFile "src/praxis.h")
