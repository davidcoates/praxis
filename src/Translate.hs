{-# LANGUAGE QuasiQuotes   #-}
{-# LANGUAGE TupleSections #-}
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


data Token = LBrace | RBrace | Semi | Text String | Crumb Source | Newline

freshTempVar :: Praxis Name
freshTempVar = (++ "_") <$> freshVar "temp"

ty :: (Term a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
ty = annotation . just

indent :: Int -> String
indent n = replicate (2*n) ' '

layout :: [Token] -> String
layout = layout' 0 "" where

  layout' :: Int -> String -> [Token] -> String
  layout' depth prefix ts = case ts of

    LBrace : ts -> "{" ++ layout' (depth + 1) ("\n" ++ indent (depth + 1)) ts

    RBrace : ts -> "\n" ++ indent (depth - 1) ++ "}" ++ layout' (depth - 1) "" ts

    Semi : ts -> ";" ++ layout' depth ("\n" ++ indent depth) ts

    Text t : ts -> prefix ++ t ++ layout' depth "" ts

    Crumb src : ts -> prefix ++ "/* " ++ show src ++ " */" ++ layout' depth ("\n" ++ indent depth) ts

    Newline : ts -> "\n" ++ layout' depth (indent depth) ts

    [] -> ""


runProgram :: Annotated Program -> Praxis String
runProgram program = save stage $ do
  stage .= Translate
  program <- layout <$> translateProgram program
  display program `ifFlag` debug
  return program


translateProgram :: Annotated Program -> Praxis [Token]
translateProgram (_ :< Program decls) = foldMapA (translateDecl True) decls


-- QViewVar's with a ref domain (e.g. &r) are not needed past the type checking stage. They are dropped from the translated code.
canTranslateQTyVar :: Annotated QTyVar -> Bool
canTranslateQTyVar qTyVar = case view value qTyVar of
  QViewVar Ref _ -> False
  _              -> True

translatableQTyVars :: [Annotated QTyVar] -> [Annotated QTyVar]
translatableQTyVars = filter canTranslateQTyVar

translateQTyVar :: Annotated QTyVar -> Praxis [Token]
translateQTyVar (_ :< q) = case q of

  QTyVar n              -> return [ Text "typename ", Text n ]

  QViewVar RefOrValue n -> return [ Text "praxis::View ", Text n ]


translateView :: Annotated View -> Praxis [Token]
translateView (_ :< view) = case view of

  ViewValue            -> return [ Text "praxis::View::VALUE" ]

  ViewRef _            -> return [ Text "praxis::View::REF" ]

  ViewVar Ref _        -> return [ Text "praxis::View::REF" ]

  ViewVar RefOrValue n -> return [ Text n ]


translateType :: Annotated Type -> Praxis [Token]
translateType (_ :< t) = case t of

  TyApply t1 t2
    | (_ :< TyView view) <- t1 -> do
      view <- translateView view
      t2 <- translateType t2
      return $ [ Text "praxis::apply<" ] ++ view ++ [ Text ", " ] ++ t2 ++ [ Text ">" ]

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
      "Array"  -> "praxis::Array"
      "Char"   -> "char"
      "Bool"   -> "bool"
      "String" -> "praxis::String"
      _        -> n

  TyFun t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ [ Text "std::function<" ] ++ t2 ++ [ Text "(" ] ++ t1 ++ [ Text ")>" ]

  TyPair t1 t2 -> do
    t1 <- translateType t1
    t2 <- translateType t2
    return $ [ Text "praxis::Pair<" ] ++ t1 ++ [ Text ", " ] ++ t2 ++ [ Text ">" ]

  TyUnit -> return [ Text "praxis::Unit" ]

  TyVar n -> return [ Text n ]

  TyView v -> translateView v


translateQType :: Annotated QType -> Praxis [Token]
translateQType ((src, _) :< Forall vs _ t) = translateQType' (translatableQTyVars vs) where
  translateQType' vs
    | [] <- vs = translateType t
    | otherwise = do
      vs <- mapM translateQTyVar vs
      t <- translateType t
      return $ [ Text "template<" ] ++ intercalate [ Text ", " ] vs ++ [ Text "> " ] ++ t


translateDeclData :: Name -> Maybe (Annotated TyPat) -> [Annotated DataCon] -> Praxis [Token]
translateDeclData name tyPat alts = do

  let tyPats = case tyPat of { Just tyPat -> unpackTyPat tyPat; Nothing -> []; }

  alts <- mapM (\(_ :< DataCon name ty) -> (name,) <$> translateType ty) alts

  let
    tyPatsDecl = case tyPats of
      [] -> []
      _  -> [ Text "template<" ] ++ intercalate [ Text ", " ] (map tyPatDecl tyPats) ++ [ Text ">", Newline ]

    tyPatsInst = case tyPats of
      [] -> []
      _  -> [ Text "<" ] ++ intercalate [ Text ", " ] (map tyPatInst tyPats) ++ [ Text ">" ]

    forwardDecl = tyPatsDecl ++ [ Text "struct ", Text name, Text "Impl", Semi ] ++ tyPatsDecl ++ [ Text "using ", Text name, Text " = praxis::Box<", Text name, Text "Impl" ] ++ tyPatsInst ++ [ Text ">", Semi ]
    variantTy = [ Text "std::variant<" ] ++ intercalate [ Text ", " ] (map snd alts) ++ [ Text ">" ]
    body = [ Text "using " ] ++ variantTy ++ [ Text "::variant", Semi ] ++ [ Text "template<size_t index>", Newline, Text "inline const auto& get() const { return std::get<index>(*this); }", Newline, Text "template<size_t index>", Newline, Text "inline auto& get() { return std::get<index>(*this); }" ]
    defn = tyPatsDecl ++ [ Text "struct ", Text name, Text "Impl", Text " : " ] ++ variantTy ++ [ Text " ", LBrace ] ++ body ++ [ RBrace, Semi ]

    indices = concat [ [ Text "static constexpr size_t ", Text name, Text " = ", Text (show i), Semi ] | (name, i) <- zip (map fst alts) [0..] ]

    selfTy = [ Text name ] ++ tyPatsInst
    selfImplTy = [ Text name, Text "Impl" ] ++ tyPatsInst

    mkConstructorBody :: Name -> [Token] -> [Token]
    mkConstructorBody name ty = [ Text "std::function([](" ] ++ ty ++ [ Text "&& arg) -> "] ++ selfTy ++ [ Text " ", LBrace, Text "return praxis::mkBox<" ] ++ selfImplTy ++ [ Text ">(std::in_place_index<", Text name, Text ">, std::move(arg))", Semi, RBrace, Text ")" ]

    mkConstructor :: Name -> [Token] -> [Token]
    mkConstructor name ty = [ Text "auto mk", Text name, Text " = " ] ++ case tyPats of
      [] -> mkConstructorBody name ty
      _  -> [ Text "[]<" ] ++ intercalate [ Text ", " ] (map tyPatDecl tyPats) ++ [ Text ">()", LBrace, Text "return " ] ++ mkConstructorBody name ty ++ [ Semi, RBrace, Semi ]

    constructors = concat [ mkConstructor name ty | (name, ty) <- alts ]

  return $ forwardDecl ++ defn ++ indices ++ constructors

  where
    tyPatDecl :: Annotated TyPat -> [Token]
    tyPatDecl tyPat = case view value tyPat of
      TyPatVar name                -> [ Text "typename ", Text name ]
      TyPatViewVar RefOrValue name -> [ Text "praxis::View ", Text name ]

    tyPatInst :: Annotated TyPat -> [Token]
    tyPatInst tyPat = case view value tyPat of
      TyPatVar name                -> [ Text name ]
      TyPatViewVar RefOrValue name -> [ Text name ]

    -- unpack to a list of TyPatVar and TyPatViewVar, skipping Ref domain TyPatViewVar
    unpackTyPat :: Annotated TyPat -> [Annotated TyPat]
    unpackTyPat tyPat = case view value tyPat of
      TyPatPack p1 p2           -> unpackTyPat p1 ++ unpackTyPat p2
      TyPatVar _                -> [tyPat]
      TyPatViewVar RefOrValue _ -> [tyPat]
      TyPatViewVar Ref _        -> []


translateDecl :: Bool -> Annotated Decl -> Praxis [Token]
translateDecl topLevel ((src, _) :< decl) = case decl of

  DeclRec decls -> do
    rec0 <- freshTempVar
    rec1 <- freshTempVar
    let unpack :: Name -> [Token]
        unpack rec = [ Text "auto [" ] ++ intersperse (Text ", ") [ Text name | (_ :< DeclVar name _ _) <- decls ] ++ [ Text "] = ", Text rec, Text "(", Text rec, Text ")", Semi ]
    typeHint <- recTypeHint decls
    decls <- mapM (\(_ :< DeclVar _ sig exp) -> ([ Crumb src ] ++) <$> translateDeclVarBody sig (unpack rec1) False exp) decls
    return $ [ Text "auto ", Text rec0, Text " = " ] ++ captureList topLevel ++ [ Text "(auto ", Text rec1, Text ")" ] ++ typeHint ++ [ LBrace, Text "return std::tuple", LBrace ] ++ intercalate [ Text ",", Newline ] decls ++ [ RBrace, Semi, RBrace, Semi ] ++ unpack rec0

  DeclVar name sig exp -> do
    body <- translateDeclVarBody sig [] topLevel exp
    return $ [ Crumb src, Text "auto ", Text name, Text " = " ] ++ body ++ [ Semi ]

  DeclData name tyPat alts -> translateDeclData name tyPat alts

  DeclEnum name alts -> do
    return $ [ Text "enum ", Text name, Text " ", LBrace ] ++ intersperse (Text ", ") [ Text alt | alt <- alts ] ++ [ RBrace, Semi ]

  where
    templateVars :: Maybe (Annotated QType) -> [Annotated QTyVar]
    templateVars sig = case sig of
      Nothing                   -> []
      Just (_ :< Forall vs _ _) -> translatableQTyVars vs

    isTemplated :: Maybe (Annotated QType) -> Bool
    isTemplated = not . null . templateVars

    translateDeclVarBody :: Maybe (Annotated QType) -> [Token] -> Bool -> Annotated Exp -> Praxis [Token]
    translateDeclVarBody sig recPrefix nonLocal exp = case templateVars sig of
      [] -> translateExp' recPrefix nonLocal exp
      vs -> do
        vs <- mapM translateQTyVar vs
        exp <- translateExp' recPrefix False exp
        return $ captureList nonLocal ++ [ Text "<" ] ++ intercalate [ Text ", " ] vs ++ [ Text ">()", LBrace, Text "return " ] ++ exp ++ [ Semi, RBrace ]

    -- TODO auto deduction may not work if some decls are templated but some arent?
    recTypeHint :: [Annotated Decl] -> Praxis [Token]
    recTypeHint decls
      | all (\(_ :< DeclVar _ sig _) -> not (isTemplated sig)) decls
        = do
          -- all decls are non-templated
          tys <- mapM (\(_ :< DeclVar _ _ exp) -> translateType (view ty exp)) decls
          return $ [ Text " -> std::tuple<" ] ++ intercalate [ Text ", " ] tys ++ [ Text "> " ]
      | otherwise
        = return []


translateLit :: Lit -> Praxis [Token]
translateLit lit = return [ Text (translateLit' lit) ] where
  translateLit' lit = case lit of
    Bool bool     -> if bool then "true" else "false"
    Char char     -> show char
    Int int       -> show int
    String string -> show string

captureList :: Bool -> [Token]
captureList nonLocal = [ Text (if nonLocal then "[]" else "[&]") ]

lambdaWrap :: Bool -> [Token] -> [Token]
lambdaWrap nonLocal body = captureList nonLocal ++ [ Text "()", LBrace ] ++ body ++ [ RBrace, Text "()" ]

translateExp :: Bool -> Annotated Exp -> Praxis [Token]
translateExp = translateExp' []

translateExp' :: [Token] -> Bool -> Annotated Exp -> Praxis [Token]
translateExp' recPrefix nonLocal ((src, Just expTy) :< exp) = case exp of

  Apply exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ exp1 ++ [ Text "(" ] ++ exp2 ++ [ Text ")" ]

  Case exp alts -> do
    tempVar <- freshTempVar
    exp <- translateExp False exp
    alts <- translateCase src tempVar alts
    return $ lambdaWrap nonLocal ([ Text "auto ", Text tempVar, Text " = "] ++ exp ++ [ Semi ] ++ alts)

  Cases alts -> do
    tempVar <- freshTempVar
    let (_ :< TyFun tempVarTy _) = expTy
    tempVarTy <- translateType tempVarTy
    alts <- translateCase src tempVar alts
    return $ [ Text "std::function(" ] ++ captureList nonLocal ++ [ Text "(" ] ++ tempVarTy ++ [ Text " ", Text tempVar, Text ")", LBrace ] ++ recPrefix ++ alts ++ [ RBrace, Text ")" ]

  Con name -> do
    case expTy of
      (_ :< TyFun _ _) -> return [ Text "mk", Text name ]
      _                -> return [ Text name ]

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

  Lambda pat exp -> do
    patTy <- translateType (view ty pat)
    tempVar <- freshTempVar
    body <- translateBind tempVar pat exp
    return $ [ Text "std::function(" ] ++ captureList nonLocal ++ [ Text "(" ] ++ patTy ++ [ Text " ", Text tempVar, Text ")", LBrace ] ++ recPrefix ++ body ++ [ RBrace, Text ")" ]

  Let (_ :< Bind pat exp1) exp2 -> do
    tempVar <- freshTempVar
    exp1 <- translateExp False exp1
    bind <- translateBind tempVar pat exp2
    return $ lambdaWrap nonLocal ([ Text "auto ", Text tempVar, Text " = " ] ++ exp1 ++ [ Semi ] ++ bind)

  Lit lit -> translateLit lit

  Read name exp -> do
    tempVar <- freshTempVar
    exp <- translateExp False exp
    return $ lambdaWrap nonLocal ([ Text "const auto& ", Text tempVar, Text " = ", Text name, Semi, Text "auto ", Text name, Text " = praxis::ref(", Text tempVar, Text ")", Semi, Text "return " ] ++ exp ++ [ Semi ])

  Pair exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ [ Text "praxis::mkPair(" ] ++ exp1 ++ [ Text ", " ] ++ exp2 ++ [ Text ")" ]

  Seq exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ [ Text "(" ] ++ exp1 ++ [ Text ", " ] ++ exp2 ++ [ Text ")" ]

  Sig exp _ -> translateExp nonLocal exp

  Specialise exp specialisation -> do
    exp <- translateExp nonLocal exp
    let tyArgs = [ t | (qTyVar, t) <- specialisation, canTranslateQTyVar qTyVar ]
    tyArgs <- mapM translateType tyArgs
    return $ case tyArgs of
      [] -> exp
      _  -> exp ++ [ Text ".template operator()<" ] ++ intercalate [ Text ", " ] tyArgs ++ [ Text ">()" ]

  Switch alts -> do
    alts <- translateSwitch src alts
    return $ lambdaWrap nonLocal alts

  Unit -> return [ Text "praxis::Unit{}" ]

  Var var -> do
    return [ Text ("std::move(" ++ var ++ ")") ]

  Where exp decls -> do
    decls <- foldMapA (translateDecl False) decls
    exp <- translateExp False exp
    return $ lambdaWrap nonLocal (decls ++ [ Text "return " ] ++ exp ++ [ Semi ])


translateSwitch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis [Token]
translateSwitch src [] = return $ [ Text ("throw praxis::SwitchFail(\"" ++ show src ++ "\")"), Semi ]
translateSwitch src ((cond, exp):alts) = do
  cond <- translateExp False cond
  exp <- translateExp False exp
  alts <- translateSwitch src alts
  return $ [ Text "if (" ] ++ cond ++ [ Text ") ", LBrace, Text "return " ] ++ exp ++ [ Semi, RBrace, Newline ] ++ alts


translateCase :: Source -> Name -> [(Annotated Pat, Annotated Exp)] -> Praxis [Token]
translateCase src _ [] = return $ [ Text ("throw praxis::CaseFail(\"" ++ show src ++ "\")"), Semi ]
translateCase src var ((pat, exp):alts) =  do
  exp <- translateExp False exp
  onMatch <- translateTryMatch var pat ([ Text "return " ] ++ exp ++ [ Semi ])
  onNoMatch <- translateCase src var alts
  return $ onMatch ++ onNoMatch


translateBind :: Name -> Annotated Pat -> Annotated Exp -> Praxis [Token]
translateBind var pat exp = do
  let src = view source pat
  exp <- translateExp False exp
  pat <- translateTryMatch var pat ([ Text "return " ] ++ exp ++ [ Semi ])
  return $ pat ++ [ Text ("throw praxis::BindFail(\"" ++ show src ++ "\")"), Semi ]


translateTryMatch :: Name -> Annotated Pat -> [Token] -> Praxis [Token]
translateTryMatch var ((_, Just patTy) :< pat) onMatch = case pat of

  PatAt var' pat -> do
    pat <- translateTryMatch var' pat onMatch
    return $ [ Text "auto ", Text var', Text " = ", Text ("std::move(" ++ var ++ ")"), Semi ] ++ pat

  PatData name pat -> do
    tempVar <- freshTempVar
    onMatch <- translateTryMatch tempVar pat onMatch
    return $ [ Text "if (", Text (var ++ ".index()"), Text " == ", Text name, Text ") ", LBrace, Text "auto ", Text tempVar, Text " = ", Text var, Text ".template get<", Text name, Text ">()", Semi ] ++ onMatch ++ [ RBrace, Newline ]

  PatEnum name -> do
    return $ [ Text "if (", Text var, Text " == ", Text name, Text ") ", LBrace ] ++ onMatch ++ [ RBrace, Newline ]

  PatHole -> return onMatch

  PatLit lit -> do
    lit <- translateLit lit
    return $ [ Text "if (", Text var, Text " == " ] ++ lit ++ [ Text ") ", LBrace ] ++ onMatch ++ [ RBrace, Newline ]

  PatPair pat1 pat2 -> do
    var1 <- freshTempVar
    var2 <- freshTempVar
    pat2 <- translateTryMatch var2 pat2 onMatch
    onMatch <- translateTryMatch var1 pat1 pat2
    return $
      [ Text "auto ", Text var1, Text " = ", Text (var ++ ".first()"), Semi ] ++
      [ Text "auto ", Text var2, Text " = ", Text (var ++ ".second()"), Semi ] ++
      onMatch

  PatUnit -> return onMatch

  PatVar var' -> return $ [ Text "auto ", Text var', Text " = ", Text ("std::move(" ++ var ++ ")"), Semi ] ++ onMatch


-- FIXME a lot of this should be moved to Inbuilts

prelude = [r|/* prelude */
#include <utility>
#include <vector>
#include <string>
#include <stdexcept>
#include <functional>
#include <optional>
#include <iostream>
#include <memory>
#include <variant>

namespace praxis {

template<size_t I, typename F>
decltype(auto) recursive(F f);

template<size_t I, size_t J, typename F>
struct Recursive
{
  F f;

  explicit Recursive(F f)
    : f(f)
  {}

  template<typename... Args>
  decltype(auto) operator()(Args&&... args) const
  {
    return std::get<J>(std::apply(this->f, recursive<I, F>(this->f)))(std::forward<Args>(args)...);
  }
};

template<size_t I, typename F, size_t... Is>
decltype(auto) recursive_helper(F f, std::index_sequence<Is...>)
{
  return std::tuple<Recursive<I, Is, F>...>(
    Recursive<I, Is, F>(f)...
  );
}

template<size_t I, typename F>
auto recursive(F f)
{
  return recursive_helper<I, F>(f, std::make_index_sequence<I>{});
}

using String = std::string;

template<typename T>
struct Copy
{
  static constexpr bool value = false;
};

template<>
struct Copy<int>
{
  static constexpr bool value = true;
};

template<>
struct Copy<char>
{
  static constexpr bool value = true;
};

template<>
struct Copy<bool>
{
  static constexpr bool value = true;
};

template<>
struct Copy<const char *>
{
  static constexpr bool value = true;
};

template<typename T>
inline constexpr bool can_copy = Copy<T>::value;

template<typename T>
struct Boxed : public std::unique_ptr<T>
{
  Boxed(std::unique_ptr<T>&& ptr)
    : std::unique_ptr<T>(std::move(ptr))
  {
  }

  inline auto&& first()
  {
    return static_cast<std::unique_ptr<T>*>(this)->get()->first();
  }

  inline auto&& second()
  {
    return static_cast<std::unique_ptr<T>*>(this)->get()->second();
  }

  inline const auto& first() const
  {
    return static_cast<const std::unique_ptr<T>*>(this)->get()->first();
  }

  inline const auto& second() const
  {
    return static_cast<const std::unique_ptr<T>*>(this)->get()->second();
  }

  template<size_t index>
  inline auto&& get()
  {
    return static_cast<std::unique_ptr<T>*>(this)->get()->template get<index>();
  }

  template<size_t index>
  inline const auto& get() const
  {
    return static_cast<const std::unique_ptr<T>*>(this)->get()->template get<index>();
  }

  inline auto index() const
  {
    return static_cast<const std::unique_ptr<T>*>(this)->get()->index();
  }
};

template<typename T>
using Box = typename std::conditional<can_copy<T>, T, Boxed<T>>::type;

template<typename T, typename... Args>
auto mkBox(Args&&... args) -> Box<T>
{
  if constexpr (can_copy<T>)
    return T(std::forward<Args>(args)...);
	else
		return Boxed<T>(std::make_unique<T>(std::forward<Args>(args)...));
}

template<typename T>
struct Ref;

enum class View
{
    VALUE,
    REF
};

template<View view, typename T>
struct Apply
{
};

template<typename T>
struct Apply<View::VALUE, T>
{
  using Type = T;
};

template<typename T>
struct Apply<View::REF, T>
{
  using Type = typename std::conditional<can_copy<T>, T, Ref<T>>::type;
};

template<>
struct Apply<View::REF, String>
{
  using Type = const char *;
};

template<View view, typename T>
using apply = typename Apply<view, T>::Type;

template<typename T>
auto ref(const T& obj) -> apply<View::REF, T>
{
  if constexpr (can_copy<T>)
    return obj;
  else if constexpr (std::is_same_v<T, String>)
    return Ref(obj.data());
  else
    return Ref(&obj);
}

template<typename T>
struct Ref
{
  explicit Ref(const T* data)
    : data(data)
  {}

  inline auto first() const
  {
    return ref(data->first());
  }

  inline auto second() const
  {
    return ref(data->second());
  }

  template<size_t index>
  inline auto get() const
  {
    return ref(data->template get<index>());
  }

  inline auto index() const
  {
    return data->index();
  }

  const T* data;
};

template<typename T>
struct Copy<Ref<T>>
{
  static constexpr bool value = true;
};

struct Unit
{
};

template<>
struct Copy<Unit>
{
  static constexpr bool value = true;
};

template<typename T1, typename T2>
struct PairImpl
{
  using Tag = void;

  template<typename S1, typename S2>
  PairImpl(S1&& first, S2&& second)
    : first_(std::forward<S1>(first))
    , second_(std::forward<S2>(second))
  {}

  inline T1&& first() { return std::move(first_); }
  inline const T1& first() const { return first_; }

  inline T2&& second() { return std::move(second_); }
  inline const T2& second() const { return second_; }

  friend std::ostream& operator<< (std::ostream& ostream, const PairImpl& pair)
  {
    ostream << "(" << pair.first_ << ", " << pair.second_ << ")";
    return ostream;
  }

private:
  T1 first_;
  T2 second_;
};

template<typename T1, typename T2>
struct Copy<PairImpl<T1, T2>>
{
  static constexpr bool value = can_copy<T1> && can_copy<T2>;
};

template<typename T1, typename T2>
using Pair = Box<PairImpl<T1, T2>>;

template<class T1, class T2>
auto mkPair(T1&& first, T2&& second) -> Pair<std::decay_t<T1>, std::decay_t<T2>>
{
	return mkBox<PairImpl<std::decay_t<T1>, std::decay_t<T2>>>(std::move(first), std::move(second));
}

struct Exception : public std::runtime_error
{
  using std::runtime_error::runtime_error;
};

struct BindFail : public Exception
{
  using Exception::Exception;
};

struct CaseFail : public Exception
{
  using Exception::Exception;
};

struct SwitchFail : public Exception
{
  using Exception::Exception;
};

} // namespace praxis

#define BINARY_OP(name, ret_type, lhs_type, rhs_type, op) ret_type name(praxis::Pair<lhs_type, rhs_type> args) { return args.first() op args.second(); }
#define UNARY_OP(name, ret_type, arg_type, op) ret_type name(arg_type arg) { return op arg; }

BINARY_OP(add_int, int, int, int, +);
BINARY_OP(subtract_int, int, int, int, -);
BINARY_OP(multiply_int, int, int, int, *);
UNARY_OP(negate_int, int, int, -);
UNARY_OP(unary_plus_int, int, int, +);
BINARY_OP(lt_int, bool, int, int, <);
BINARY_OP(gt_int, bool, int, int, >);
BINARY_OP(lte_int, bool, int, int, <);
BINARY_OP(gte_int, bool, int, int, >=);
BINARY_OP(eq_int, bool, int, int, ==);
BINARY_OP(neq_int, bool, int, int, !=);

#undef UNARY_OP
#undef BINARY_OP

/*
std::function<int()> get_int = []()
{
  int x;
  std::cin >> x;
  if (std::cin.fail())
    throw praxis::Exception("get_int: no parse");
  return x;
};

std::function<std::string()> get_str = []()
{
  std::string x;
  std::cin >> x;
  if (std::cin.fail())
    throw praxis::Exception("get_str: no parse");
  return x;
};

std::function<void(int)> put_int = [](auto x)
{
  std::cout << x;
};

std::function<void(const char*)> put_str = [](auto x)
{
  std::cout << x;
};

std::function<void(const char*)> put_str_ln = [](auto x)
{
  std::cout << x << std::endl;
};
*/

auto print = []<typename T>() -> std::function<praxis::Unit(praxis::apply<praxis::View::REF, T>)>
{
  return [=](T t) -> praxis::Unit
  {
    std::cout << t << std::endl;
    return praxis::Unit{};
  };
};

/* prelude end */
|]
