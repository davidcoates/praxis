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
freshTempVar = (++ "_") <$> freshVar "temp"

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

  QTyVar n     -> return [ Text "typename ", Text n ]

  QViewVar _ n -> return [ Text "praxis::View ", Text n ]


-- TODO... we need to know how QTypes are specialised

translateView :: Annotated View -> Praxis [Token]
translateView (_ :< view) = case view of

  ViewValue -> return [ Text "praxis::View::VALUE" ]

  ViewRef _ -> return [ Text "praxis::View::REF" ]

  ViewVar _ n -> return [ Text n ]


translateType :: Annotated Type -> Praxis [Token]
translateType (_ :< t) = case t of

  TyApply t1 t2
    | (_ :< View view) <- t1 -> do
      view <- translateView view
      t2 <- translateType t2
      return $ [ Text "typename praxis::Apply<" ] ++ view ++ [ Text ", " ] ++ t2 ++ [ Text ">::Type" ]

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


translateQType :: Annotated QType -> Praxis [Token]
translateQType ((src, _) :< Forall vs _ t)
  | [] <- vs = translateType t
  | otherwise = do
    vs <- mapM translateQTyVar vs
    t <- translateType t
    return $ [ Text "template<" ] ++ intercalate [ Text ", " ] vs ++ [ Text "> " ] ++ t


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
      return $ [ Crumb src ] ++ [ Text "extern " ] ++ ty ++ [ Text " ", Text name, Semi ]


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
translateExp nonLocal ((src, Just expTy) :< exp) = case exp of

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
    return $ captureList nonLocal ++ [ Text "(" ] ++ tempVarTy ++ [ Text " ", Text tempVar, Text ")", LBrace ] ++ alts ++ [ RBrace ]

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

  Lambda pat exp -> do
    patTy <- translateType (view ty pat)
    tempVar <- freshTempVar
    body <- translateBind tempVar pat exp
    return $ captureList nonLocal ++ [ Text "(" ] ++ patTy ++ [ Text " ", Text tempVar, Text ")", LBrace ] ++ body ++ [ RBrace ]

  Let (_ :< Bind pat exp1) exp2 -> do
    tempVar <- freshTempVar
    exp1 <- translateExp False exp1
    bind <- translateBind tempVar pat exp2
    return $ lambdaWrap nonLocal ([ Text "auto ", Text tempVar, Text " = " ] ++ exp1 ++ [ Semi ] ++ bind)

  Lit lit -> translateLit lit

  Read _ exp -> translateExp nonLocal exp

  Pair exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ [ Text "praxis::Pair(" ] ++ exp1 ++ [ Text ", " ] ++ exp2 ++ [ Text ")" ]

  Seq exp1 exp2 -> do
    exp1 <- translateExp nonLocal exp1
    exp2 <- translateExp nonLocal exp2
    return $ [ Text "(" ] ++ exp1 ++ [ Text ", " ] ++ exp2 ++ [ Text ")" ]

  Sig exp _ -> translateExp nonLocal exp

  -- TODO
  Switch alts -> do
    alts <- translateSwitch src alts
    return $ lambdaWrap nonLocal alts

  Unit -> return [ Text "praxis::Unit{}" ]

  -- FIXME if this is a poly function, we need to specify template parameters!
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
  return $ [ Text "if (" ] ++ cond ++ [ Text ")", LBrace, Text "return " ] ++ exp ++ [ Semi, RBrace ] ++ alts


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

  PatCon con pat -> do
    conType <- translateType patTy
    let tag = conType ++ [ Text ("::Tag::" ++ con) ]
    tempVar <- freshTempVar
    onMatch <- case pat of { Just pat -> translateTryMatch tempVar pat onMatch; Nothing -> return onMatch; }
    return $ [ Text "if (", Text (var ++ ".tag()"), Text " == " ] ++ tag ++ [ Text ")", LBrace, Text "auto ", Text tempVar, Text " = ", Text (var ++ ".template get<") ] ++ tag ++ [ Text ">()", Semi ] ++ onMatch ++ [ RBrace ]

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
      [ Text "auto ", Text var1, Text " = ", Text (var ++ ".first()"), Semi ] ++
      [ Text "auto ", Text var2, Text " = ", Text (var ++ ".second()"), Semi ] ++
      onMatch

  PatUnit -> return onMatch

  PatVar var' -> return $ [ Text "auto ", Text var', Text " = ", Text ("std::move(" ++ var ++ ")"), Semi ] ++ onMatch


prelude :: String
prelude = [r|/* prelude */
#include <utility>
#include <vector>
#include <string>
#include <stdexcept>
#include <functional>
#include <optional>
#include <iostream>

namespace praxis {

using String = std::string;

template<typename T>
struct Copy
{
  static constexpr bool value = true;
};

template<typename T>
inline constexpr bool can_copy = Copy<T>::value;

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
    return ref(data->first());
  }

  inline auto tag() const
  {
    return data->tag();
  }

  template<typename S>
  inline auto get() const
  {
    return ref(data->template get<S>());
  }

  using Tag = typename T::Tag;

  const T* data;
};

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
  using Type = typename std::conditional<Copy<T>::value, T, const T*>::type;
};

template<>
struct Apply<View::REF, String>
{
  using Type = const char *;
};

template<typename T>
auto ref(const T& obj) -> typename Apply<View::REF, T>::Type
{
  if constexpr (can_copy<T>)
  {
    return obj;
  }
  else if constexpr (std::is_same_v<T, String>)
  {
    return Ref(obj.data());
  }
  else
  {
    return Ref(&obj);
  }
}

struct Unit
{
};

template<typename T1, typename T2>
struct Pair
{
  using Tag = void;

  template<typename S1 = T1, typename S2 = T2>
  Pair(S1&& first, S2&& second)
    : first_(std::forward<S1>(first))
    , second_(std::forward<S2>(second))
  {}

  inline T1& first() { return first_; }
  inline const T1& first() const { return first_; }

  inline const T2& second() const { return second_; }
  inline T2& second() { return second_; }

  friend std::ostream& operator<< (std::ostream& ostream, const Pair& pair)
  {
    ostream << "(" << pair.first_ << ", " << pair.second_ << ")";
    return ostream;
  }

private:
  T1 first_;
  T2 second_;
};

template<class T1, class T2>
Pair(T1, T2) -> Pair<std::decay_t<T1>, std::decay_t<T2>>;

template<typename T1, typename T2>
struct Copy<Pair<T1, T2>>
{
  static constexpr bool value = can_copy<T1> && can_copy<T2>;
};

struct BindFail : public std::runtime_error
{
  using std::runtime_error::runtime_error;
};

struct CaseFail : public std::runtime_error
{
  using std::runtime_error::runtime_error;
};

struct SwitchFail : public std::runtime_error
{
  using std::runtime_error::runtime_error;
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

// get_int
// get_contents
// put_int
// put_str
// put_str_ln
// compose

/* prelude end */
|]
