{-# LANGUAGE TemplateHaskell #-}

-- | The grammar definition for Praxis terms.

module Syntax.Term
  ( syntax
  ) where

import           Common
import           Introspect
import           Stage
import           Syntax.Prism
import           Syntax.Syntax
import           Syntax.TH
import           Term
import           Token

import           Data.List     (intersperse)
import           Data.Maybe    (catMaybes)
import qualified Data.Set      as Set (fromList, toList)
import           Prelude       hiding (_Just, exp, pure, until, (*>), (<$>),
                                (<*), (<*>))


until :: Syntax f => f a -> f () -> f [a]
until p q = _Nil <$> q <|> _Cons <$> p <*> until p q

token :: Syntax f => Token -> f ()
token t = match (\t' -> if t' == t then Just () else Nothing) (const t)

special :: Syntax f => Char -> f ()
special c = token (Special c) <|> expected ("special '" ++ [c] ++ "'")

layout :: Syntax f => Char -> f ()
layout c = token (Layout c) <|> expected ("layout '" ++ [c] ++ "'")

block :: Syntax f => f a -> f [a]
block p = layout '{' *> _Cons <$> p <*> (layout ';' *> p) `until` layout '}'

blockOrLine :: Syntax f => f a -> f [a]
blockOrLine f =
  _Cons <$> layout '{' *> f <*> (layout ';' *> f) `until` layout '}' <|>
  _Cons <$> f <*> _Nil <$> pure ()

blockLike :: Syntax f => f () -> f a -> f [a]
blockLike f g =
  f *> blockOrLine g <|>
  _Nil <$> pure ()

keyword :: Syntax f => Keyword -> f ()
keyword kw = token (Keyword kw) <|> expected ("keyword '" ++ keywordString kw ++ "'")

contextual :: Syntax f => String -> f ()
contextual str = token (Ident Plain str) <|> expected ("contextual keyword '" ++ str ++ "'")

conId :: Syntax f => f Name
conId = match f (Ident Plain . nameString) where
  f = \case
    Ident Plain str | isUpper (head str) -> Just (mkName str)
    _                                    -> Nothing

varId :: Syntax f => f Name
varId = match f (Ident Plain . nameString) where
  f = \case
    Ident Plain str | isLower (head str) -> Just (mkName str)
    _                                    -> Nothing

tyVarId :: Syntax f => f (Flavor, Name)
tyVarId = match f (\(flavor, name) -> Ident flavor (nameString name)) where
  f = \case
    Ident flavor str | isLower (head str) -> Just (flavor, mkName str)
    _                                     -> Nothing

varIdRef :: Syntax f => f Name
varIdRef = match f (Ident Ref . nameString) where
  f = \case
    Ident Ref str -> Just (mkName str)
    _             -> Nothing

symbol :: Syntax f => f Name
symbol = match f (Ident Plain . nameString) where
  f = \case
    Ident Plain str | isSymbol (head str) -> Just (mkName str)
    _                                     -> Nothing

internal :: Syntax f => String -> f ()
internal str = match (const Nothing) (const (Internal (pretty str)))

kindUni :: Syntax f => f Name
kindUni = match (const Nothing) (Internal . pretty . nameString)

tyUni :: Syntax f => f (Flavor, Name)
tyUni = match (const Nothing) (\(flavor, name) -> Internal (pretty (Ident flavor (nameString name))))

inbuilt :: Syntax f => f Inbuilt
inbuilt = match (const Nothing) (Ident Plain . show)

integer :: Syntax f => f Integer
integer = match f (Token.Lit . Integer) where
  f = \case
    Token.Lit (Integer n) -> Just n
    _                     -> Nothing

lit :: Syntax f => f Lit
lit = match f Token.Lit where
  f = \case
    Token.Lit lit -> Just lit
    _             -> Nothing

litNoString :: Syntax f => f Lit
litNoString = match f Token.Lit where
  f = \case
    Token.Lit (String _) -> Nothing
    Token.Lit lit        -> Just lit
    _                    -> Nothing


definePrisms ''Assoc
definePrisms ''Op
definePrisms ''OpRules
definePrisms ''Prec

definePrisms ''Bool
definePrisms ''Ordering
definePrisms ''TypeInstance

definePrisms ''Bind
definePrisms ''DataCon
definePrisms ''DataMode
definePrisms ''Decl
definePrisms ''DeclRec
definePrisms ''DeclTerm
definePrisms ''DeclType
definePrisms ''Exp
definePrisms ''Pat
definePrisms ''Program
definePrisms ''Stmt
definePrisms ''Tok

definePrisms ''QType
definePrisms ''Type
definePrisms ''TypePat

definePrisms ''Kind

definePrisms ''KindConstraint
definePrisms ''TypeConstraint

definePrisms ''Requirement

-- | The syntax for a given term type.
syntax :: (SyntaxT f s, IsTerm a) => TermT a -> f (a s)
syntax = \case
  -- | Operators
  OpRulesT        -> opRules
  -- | T0
  DataConT        -> dataCon
  DeclT           -> decl
  DeclRecT        -> declRec
  DeclTermT       -> declTerm
  DeclTypeT       -> declType
  ExpT            -> exp
  PatT            -> pat
  ProgramT        -> program
  StmtT           -> stmt
  TokT            -> tok
  -- | T1
  QTypeT          -> qTy
  TypeConstraintT -> typeConstraint
  TypeT           -> ty
  TypePatT        -> typePat
  -- | T2
  KindT           -> kind
  KindConstraintT -> kindConstraint
  -- | Solver
  TypeRequirementT -> typeRequirement
  KindRequirementT -> kindRequirement


tuple :: (SyntaxT f s, IsTerm a) => Prism (a s) () -> Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
tuple unit pair p = special '(' *> tuple' where
  tuple' = unit <$> special ')' *> pure () <|> rightWithSep pair p (special ',') <* special ')'

join :: (SyntaxT f s, IsTerm a) => f (a s) -> (Prism (a s) (Annotated s a, b), f b) -> f (a s)
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> printOnly p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

right :: (SyntaxT f s, IsTerm a) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
right _P p = rightWithSep _P p (pure ())

left :: (SyntaxT f s, IsTerm a) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
left _P p = leftWithSep _P p (pure ())

foldWithSep :: forall f a s. (SyntaxT f s, IsTerm a) => (Annotation s a -> [Annotated s a] -> Annotated s a) -> ((a s) -> Maybe [Annotated s a]) -> f (a s) -> f () -> f (a s)
foldWithSep fold unfold p s = Prism f g <$> blank (stageT :: StageT s) (termT :: TermT a) <*> (_Cons <$> annotated p <*> many (s *> annotated p)) <|> printOnly p where
  f :: (Annotation s a, [Annotated s a]) -> (a s)
  f (a, ps) = view value (fold a ps)
  g :: (a s) -> Maybe (Annotation s a, [Annotated s a])
  g x = case unfold x of
    Nothing     -> Nothing
    Just (x:xs) -> Just (undefined, x : xs)

rightWithSep :: forall f a s. (SyntaxT f s, IsTerm a) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f () -> f (a s)
rightWithSep _P p s = foldWithSep fold unfold p s where
  fold _ [x]    = x
  fold a (x:xs) = let y = fold a xs in (view source x <> view source y, a) :< construct _P (x, y)
  unfold  x = case destruct _P x of
    Just (x, y) -> Just (x : unfold' y)
    Nothing     -> Nothing
  unfold' x = case destruct _P (view value x) of
    Just (x, y) -> x : unfold' y
    Nothing     -> [x]

leftWithSep :: forall f a s. (SyntaxT f s, IsTerm a) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f () -> f (a s)
leftWithSep _P p s = foldWithSep fold unfold p s where
  fold _ [x]      = x
  fold a (x:y:ys) = fold a ((view source x <> view source y, a) :< construct _P (x, y) : ys)
  unfold x = case destruct _P x of
    Just (x, y) -> Just (unfold' x ++ [y])
    Nothing     -> Nothing
  unfold' x = case destruct _P (view value x) of
    Just (x, y) -> unfold' x ++ [y]
    Nothing     -> [x]

-- special sauce to make op applications right associative, but normal applications left associative e.g. &r ?v C t &r ?v t -> &r (?v ((((C t) &r) ?v) t))
foldType :: forall f s. (SyntaxT f s) => f (Type s) -> f (Type s)
foldType ty = foldWithSep fold unfold ty (pure ()) where
  fold :: Annotation s Type -> [Annotated s Type] -> Annotated s Type
  fold _ [x] = x
  fold a (x:xs)
    | isTypeOp x = let y = fold a xs in (view source x <> view source y, a) :< TypeApplyOp x y
    | otherwise = foldLeft a (x:xs)
  foldLeft _ [x] = x
  foldLeft a (x:y:ys) = fold a ((view source x <> view source y, a) :< TypeApply x y : ys)
  unfold x = case x of
    TypeApplyOp x y -> Just (x : unfold' y)
    TypeApply x y   -> Just (unfold' x ++ [y])
    _               -> Nothing
  unfold' x = case view value x of
    TypeApplyOp x y -> x : unfold' y
    TypeApply x y   -> unfold' x ++ [y]
    _               -> [x]


typeConstraint :: (SyntaxT f s) => f (TypeConstraint s)
typeConstraint =
  _TypeIsInstance <$> swap <$> annotated ty <*> keyword KeywordColon *> typeInstance <|>
  printOnly (_TypeIsEq <$> annotated ty <*> internal "~" *> annotated ty) <|>
  printOnly (_TypeIsEqIfAffine <$> annotated ty <*> internal "~" *> annotated ty <*> internal "|" *> internal "affine" *> annotated ty) <|>
  printOnly (_TypeIsIntegralOver <$> internal "integral" *> annotated ty <*> internal "over" *> integer) <|>
  printOnly (_TypeIsRef <$> internal "ref" *> annotated ty) <|>
  printOnly (_TypeIsRefFree <$> swap <$> varId <*> internal "∉" *> internal "lifetimes" *> annotated ty) <|>
  printOnly (_TypeIsSub <$> annotated ty <*> internal "<:" *> annotated ty) <|>
  printOnly (_TypeIsSubIfAffine <$> annotated ty <*> internal "<:" *> annotated ty <*> internal "|" *> annotated ty) <|>
  printOnly (_TypeIsValue <$> internal "value" *> annotated ty) <|>
  expected "type constraint"

kindConstraint :: (SyntaxT f s) => f (KindConstraint s)
kindConstraint =
  printOnly (_KindIsEq <$> annotated kind <*> internal "~" *> annotated kind) <|>
  printOnly (_KindIsPlain <$> internal "plain" *> annotated kind) <|>
  printOnly (_KindIsSub <$> annotated kind <*> internal "<:" *> annotated kind) <|>
  expected "kind constraint"

program :: (SyntaxT f s) => f (Program s)
program = _Program <$> block (annotated decl) <|> expected "program"

decl :: (SyntaxT f s) => f (Decl s)
decl =
  _DeclRec <$> keyword KeywordRec *> blockOrLine (annotated declRec) <|>
  declSyn <|>
  declOp <|>
  _DeclTerm <$> annotated declTerm <|>
  _DeclType <$> annotated declType <|>
  expected "declaration"

declRec :: (SyntaxT f s) => f (DeclRec s)
declRec =
  _DeclRecTerm <$> annotated declTerm <|>
  _DeclRecType <$> annotated declType <|>
  expected "recursive declaration"

declOp :: (SyntaxT f s) => f (Decl s)
declOp = _DeclOpSugar <$> keyword KeywordOperator *> annotated op <*> keyword KeywordEquals *> varId <*> annotated opRules

op :: (SyntaxT f s) => f (Op s)
op = _Op <$> special '(' *> atLeast 2 atom <* special ')' <|> expected "operator section"  where
  atom = _Nothing <$> special '_' <|> _Just <$> symbol <|> expected "operator or hole"

opRules :: (SyntaxT f s) => f (OpRules s)
opRules = _OpRules <$> blockLike (keyword KeywordWhere) (_Left <$> assoc <|> _Right <$> precs) <|> expected "operator rules"

assoc :: Syntax f => f Assoc
assoc = assoc' <* contextual "associative" where
  assoc' =
    _AssocLeft <$> contextual "left" <|>
    _AssocRight <$> contextual "right"

precs :: (SyntaxT f s) => f [Annotated s Prec]
precs = blockLike (contextual "precedence") (annotated prec)

prec :: (SyntaxT f s) => f (Prec s)
prec = _Prec <$> ordering <*> annotated op where
  ordering =
    _GT <$> contextual "above" <|>
    _LT <$> contextual "below" <|>
    _EQ <$> contextual "equal"

declSyn :: (SyntaxT f s) => f (Decl s)
declSyn = _DeclSynSugar <$> keyword KeywordUsing *> conId <*> keyword KeywordEquals *> annotated ty

declType :: (SyntaxT f s) => f (DeclType s)
declType = declTypeDataSugar <|> printOnly declTypeData <|> declTypeEnum where

  declTypeData :: (SyntaxT f s) => f (DeclType s)
  declTypeData = _DeclTypeData <$> keyword KeywordDatatype *> dataMode <*> conId <*> many (annotated typePat) <*> keyword KeywordEquals *> dataCons

  declTypeDataSugar :: (SyntaxT f s) => f (DeclType s)
  declTypeDataSugar = _DeclTypeDataSugar <$> keyword KeywordDatatype *> optional dataMode <*> conId <*> many (annotated typePat) <*> keyword KeywordEquals *> dataCons

  dataCons :: (SyntaxT f s) => f [Annotated s DataCon]
  dataCons = _Cons <$> annotated dataCon <*> many (contextual "|" *> annotated dataCon)

  dataMode :: Syntax f => f DataMode
  dataMode = (_DataBoxed <$> contextual "boxed") <|> (_DataUnboxed <$> contextual "unboxed")

  declTypeEnum :: (SyntaxT f s) => f (DeclType s)
  declTypeEnum = _DeclTypeEnum <$> keyword KeywordEnum *> conId <*> keyword KeywordEquals *> alts where
    alts = _Cons <$> conId <*> many (contextual "|" *> conId)


dataCon :: (SyntaxT f s) => f (DataCon s)
dataCon = _DataCon <$> conId <*> annotated ty1

typePat :: (SyntaxT f s) => f (TypePat s)
typePat =
  _TypePatVar <$> tyVarId <|>
  expected "type variable"

declTerm :: (SyntaxT f s) => f (DeclTerm s)
declTerm = prefix varId (_DeclTermSigSugar, declTermSig) (_DeclTermDefSugar, declTermDef) <|> printOnly declTermVar <|> expected "term declaration" where
  declTermSig = keyword KeywordColon *> annotated qTy
  declTermDef = annotated pat `until` keyword KeywordEquals <*> annotated exp
  declTermVar = _DeclTermVar <$> varId <*> (_Just <$> keyword KeywordColon *> annotated qTy) <*> keyword KeywordEquals *> annotated exp

bind :: (SyntaxT f s) => f (Bind s)
bind = _Bind <$> annotated pat <*> keyword KeywordEquals *> annotated exp <|> expected "binding"

pat :: (SyntaxT f s) => f (Pat s)
pat = prefix' conId (_PatData, annotated pat0) _PatEnum <|> pat0 <|> expected "pattern" where
  pat0 =
    _PatHole <$> special '_' <|>
    _PatLit <$> litNoString <|> -- TODO allow string literals
    prefix' varId (_PatAt, keyword KeywordAt *> annotated pat) _PatVar <|>
    tuple _PatUnit _PatPair pat <|>
    expected "pattern(0)"

kind :: (SyntaxT f s) => f (Kind s)
kind = kind0 `join` (_KindFn, keyword KeywordArrow *> annotated kind) <|> expected "kind" where
  kind0 =
    _KindRef <$> keyword KeywordRef <|>
    _KindType <$> keyword KeywordType <|>
    _KindView <$> keyword KeywordView <|>
    printOnly (_KindUni <$> kindUni) <|>
    expected "kind(0)"

qTy :: (SyntaxT f s) => f (QType s)
qTy = poly <|> mono <|> expected "quantified type" where
  poly = _Poly <$> keyword KeywordForall *> some (annotated typePat) <*> typeConstraints <*> (contextual "." *> annotated ty)
  mono = _Mono <$> annotated ty
  typeConstraints :: (SyntaxT f s) => f [Annotated s TypeConstraint]
  typeConstraints = _Cons <$> (contextual "|" *> annotated typeConstraint) <*> many (special ',' *> annotated typeConstraint) <|> _Nil <$> pure ()

ty :: (SyntaxT f s) => f (Type s)
ty = ty1 `join` (_TypeFn, keyword KeywordArrow *> annotated ty) <|> expected "type"

typeInstance :: Syntax f => f TypeInstance
typeInstance = _Clone <$> keyword KeywordClone <|> _Dispose <$> keyword KeywordDispose <|> _Copy <$> keyword KeywordCopy <|> _Capture <$> keyword KeywordCapture <|> _Integral <$> keyword KeywordIntegral

ty0 :: (SyntaxT f s) => f (Type s)
ty0 =
  _TypeCon <$> conId <|>
  _TypeIdentityOp <$> keyword KeywordAt <|>
  printOnly (_TypeRef <$> varIdRef) <|>
  _TypeSetOp <$> (Prism Set.fromList (Just . Set.toList) <$> (special '{' *> (_Cons <$> annotated ty <*> some (special ',' *> annotated ty)) <* special '}')) <|>
  printOnly (_TypeUni <$> tyUni) <|>
  _TypeVar <$> tyVarId <|>
  tuple _TypeUnit _TypePair ty <|>
  expected "type(0)"

ty1 :: (SyntaxT f s) => f (Type s)
ty1 = foldType ty0 <|> expected "type(1)"

tok :: (SyntaxT f s) => f (Tok s)
tok = printOnly (_TokOp <$> symbol <|> _TokExp <$> annotated exp) <|> expected "token"

exp :: (SyntaxT f s) => f (Exp s)
exp = exp6 `join` (_Sig, keyword KeywordColon *> annotated ty) <|> expected "expression" where
  exp6 = optWhere <$> annotated exp5 <*> blockLike (keyword KeywordWhere) (annotated declTerm) <|> printOnly exp5 <|> expected "expression(6)"
  optWhere = Prism (\(e, ps) -> case ps of { [] -> view value e; _ -> Where e ps }) (\case { Where e ps -> Just (e, ps); _ -> Nothing })
  exp5 = rightWithSep _Defer exp4 (keyword KeywordDefer) <|> expected "expression(5)"
  exp4 = rightWithSep _Seq exp3 (keyword KeywordSeq) <|> expected "expression(4)"
  exp3 =
    _Read <$> keyword KeywordRead *> varId <*> keyword KeywordIn *> annotated exp <|>
    _DoSugar <$> keyword KeywordDo *> block (annotated stmt) <|>
    _Case <$> keyword KeywordCase *> annotated exp <*> keyword KeywordOf *> block alt <|>
    _Cases <$> keyword KeywordCases *> block alt <|>
    _If <$> keyword KeywordIf *> annotated exp <*> keyword KeywordThen *> annotated exp <*> keyword KeywordElse *> annotated exp <|>
    _Lambda <$> keyword KeywordLambda *> alt <|>
    printOnly (_Closure <$> empty <*> annotated exp3) <|>
    _Let <$> keyword KeywordLet *> annotated bind <*> keyword KeywordIn *> annotated exp <|>
    _Switch <$> keyword KeywordSwitch *> block switch <|>
    exp2 <|> expected "expression(3)"
  exp2 = mixfix <$> some (annotated (_TokOp <$> symbol <|> _TokExp <$> annotated exp1)) <|> printOnly exp1 <|> expected "expression(2)"
  mixfix = Prism (\ts -> case ts of { [_ :< TokExp e] -> view value e; _ -> MixfixSugar ts }) (\case { MixfixSugar ts -> Just ts; _ -> Nothing })
  exp1 = left _Apply exp0 <|> expected "expression(1)"
  exp0 =
    _VarRefSugar <$> varIdRef <|>
    _Var <$> varId <|>
    _Con <$> conId <|>
    _Inbuilt <$> inbuilt <|>
    _Lit <$> lit <|>
    printOnly (_Specialize <$> annotated exp0 <*> empty) <|>
    tuple _Unit _Pair exp <|> -- Note: Grouping parentheses are handled here
    expected "expression(0)"

switch :: (SyntaxT f s) => f (Annotated s Exp, Annotated s Exp)
switch = annotated exp <*> keyword KeywordArrow *> annotated exp <|> expected "switch alternative"

-- TODO allow "let ... in" in expression?
stmt :: (SyntaxT f s) => f (Stmt s)
stmt = _StmtBind <$> keyword KeywordLet *> annotated bind <|> _StmtExp <$> annotated exp <|> expected "statement"

alt :: (SyntaxT f s) => f (Annotated s Pat, Annotated s Exp)
alt = annotated pat <*> keyword KeywordArrow *> annotated exp <|> expected "case alternative"

typeRequirement :: (SyntaxT f s) => f (Requirement TypeConstraint s)
typeRequirement = _Requirement <$> annotated typeConstraint

kindRequirement :: (SyntaxT f s) => f (Requirement KindConstraint s)
kindRequirement = _Requirement <$> annotated kindConstraint
