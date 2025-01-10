{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

-- | The grammar definition for Praxis terms.

module Syntax.Term
  ( syntax
  ) where

import           Common
import           Introspect
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

definePrisms ''Bool
definePrisms ''Ordering

until :: Syntax f => f a -> f () -> f [a]
until p q = _Nil <$> q <|> _Cons <$> p <*> until p q

token :: Syntax f => Token -> f ()
token t = match (\t' -> if t' == t then Just () else Nothing) (const t)

special :: Syntax f => Char -> f ()
special c = token (Special c) <|> expected ("special '" ++ [c] ++ "'")

layout :: Syntax f => Char -> f ()
layout c = token (Layout c) <|> expected ("layout '" ++ [c] ++ "'")

contextualOp :: Syntax f => Name -> f ()
contextualOp op = token (VarSym op) <|> internal (reservedSym op) <|> expected ("contextual keyword '" ++ op ++ "'")

contextualId :: Syntax f => Name -> f ()
contextualId id = token (VarId id) <|> internal (reservedId id) <|> expected ("contextual keyword '" ++ id ++ "'")

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

conId :: Syntax f => f Name
conId = match f ConId where
  f = \case
    ConId n -> Just n
    _       -> Nothing

varId :: Syntax f => f Name
varId = match f VarId where
  f = \case
    VarId n -> Just n
    _       -> Nothing

flavoredVarId :: Syntax f => f (Flavor, Name)
flavoredVarId = match parse print where
  parse = \case
    VarId n      -> Just (Plain, n)
    VarIdRef n   -> Just (Ref, n)
    VarIdValue n -> Just (Value, n)
    VarIdView n  -> Just (View, n)
    _            -> Nothing
  print (f, n) = case f of
    Plain -> VarId n
    Ref   -> VarIdRef n
    Value -> VarIdValue n
    View  -> VarIdView n

varIdRef :: Syntax f => f Name
varIdRef = match f VarIdRef where
  f = \case
    VarIdRef n -> Just n
    _          -> Nothing

varSym :: Syntax f => f Name
varSym = match f VarSym where
  f = \case
    VarSym n -> Just n
    _        -> Nothing

uni :: Syntax f => f Name
uni = match (const Nothing) (Uni . VarId)

flavoredUni :: Syntax f => f (Flavor, Name)
flavoredUni = match (const Nothing) print where
  print (f, n) = Uni $ case f of
    Plain -> VarId n
    Ref   -> VarIdRef n
    Value -> VarIdValue n
    View  -> VarIdView n

lit :: Syntax f => f Lit
lit = match f Token.Lit where
  f = \case
    Token.Lit l -> Just l
    _           -> Nothing

litNoString :: Syntax f => f Lit
litNoString = match f (\l -> Token.Lit l) where
  f = \case
    Token.Lit (String _) -> Nothing
    Token.Lit l          -> Just l
    _                    -> Nothing

reservedSym :: Syntax f => String -> f ()
reservedSym s = token (ReservedSym s) <|> expected ("reserved symbol '" ++ s ++ "'")

reservedCon :: Syntax f => String -> f ()
reservedCon s = token (ReservedCon s) <|> expected ("reserved name '" ++ s ++ "'")

reservedId :: Syntax f => String -> f ()
reservedId s = token (ReservedId s) <|> expected ("reserved name '" ++ s ++ "'")

definePrisms ''Assoc
definePrisms ''Op
definePrisms ''OpRules
definePrisms ''Prec

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
syntax :: (Term a, Syntax f) => I a -> f a
syntax = \case
  -- | Operators
  IOp             -> op
  IOpRules        -> opRules
  -- | T0
  IDataCon        -> dataCon
  IDecl           -> decl
  IDeclRec        -> declRec
  IDeclTerm       -> declTerm
  IDeclType       -> declType
  IExp            -> exp
  IPat            -> pat
  IProgram        -> program
  IStmt           -> stmt
  ITok            -> tok
  -- | T1
  IQType          -> qTy
  ITypeConstraint -> typeConstraint
  IType           -> ty
  ITypePat        -> typePat
  -- | T2
  IKind           -> kind
  IKindConstraint -> kindConstraint
  -- | Solver
  ITypeRequirement -> typeRequirement
  IKindRequirement -> kindRequirement


tuple :: (Syntax f, Term a) => Prism a () -> Prism a (Annotated a, Annotated a) -> f a -> f a
tuple unit pair p = special '(' *> tuple' where
  tuple' = unit <$> special ')' *> pure () <|> rightWithSep (special ',') pair p <* special ')'

join :: (Syntax f, Term a) => f a -> (Prism a (Annotated a, b), f b) -> f a
join p (_P, q) = Prism f g <$> annotated p <*> optional q where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Just (phantom x, Nothing)

foldRight :: Prism a (Annotated a, Annotated a) -> Prism a [Annotated a]
foldRight _P = Prism (view value . fold) (Just . unfold . phantom) where
  fold [x]    = x
  fold (x:xs) = let y = fold xs in (view source x <> view source y, Nothing) :< construct _P (x, y)
  unfold x = case destruct _P (view value x) of
    Just (x, y) -> x : unfold y
    Nothing     -> [x]

foldLeft :: Prism a (Annotated a, Annotated a) -> Prism a [Annotated a]
foldLeft _P = Prism (view value . fold) (Just . unfold . phantom) where
  fold [x]      = x
  fold (x:y:ys) = fold ((view source x <> view source y, Nothing) :< construct _P (x, y) : ys)
  unfold x = case destruct _P (view value x) of
    Just (x, y) -> unfold x ++ [y]
    Nothing     -> [x]

right :: (Syntax f, Term a) => Prism a (Annotated a, Annotated a) -> f a -> f a
right = rightWithSep (pure ())

rightWithSep :: (Syntax f, Term a) => f () -> Prism a (Annotated a, Annotated a) -> f a -> f a
rightWithSep s _P p = foldRight _P <$> (_Cons <$> annotated p <*> many (s *> annotated p))

left :: (Syntax f, Term a) => Prism a (Annotated a, Annotated a) -> f a -> f a
left = leftWithSep (pure ())

leftWithSep :: (Syntax f, Term a) => f () -> Prism a (Annotated a, Annotated a) -> f a -> f a
leftWithSep s _P p = foldLeft _P <$> (_Cons <$> annotated p <*> many (s *> annotated p))

integer :: Syntax f => f Integer
integer = match f (Token.Lit . Integer) where
  f = \case
    Token.Lit (Integer n) -> Just n
    _                     -> Nothing

typeConstraint :: Syntax f => f TypeConstraint
typeConstraint =
  _TypeIsInstance <$> annotated ty <|>
  internal (_TypeIsEq <$> annotated ty <*> reservedSym "=" *> annotated ty) <|>
  internal (_TypeIsEqIfAffine <$> annotated ty <*> reservedSym "=" *> annotated ty <*> reservedSym "|" *> annotated ty) <|>
  internal (_TypeIsIntegralOver <$> swap <$> integer <*> reservedSym "∈" *> annotated ty) <|>
  internal (_TypeIsRef <$> reservedCon "Ref" *> annotated ty) <|>
  internal (_TypeIsRefFree <$> swap <$> varId <*> reservedSym "∉" *> annotated ty) <|>
  internal (_TypeIsSub <$> annotated ty <*> reservedSym "≤" *> annotated ty) <|>
  internal (_TypeIsSubIfAffine <$> annotated ty <*> reservedSym "≤" *> annotated ty <*> reservedSym "|" *> annotated ty) <|>
  internal (_TypeIsValue <$> reservedCon "Value" *> annotated ty) <|>
  expected "type constraint"

kindConstraint :: Syntax f => f KindConstraint
kindConstraint =
  internal (_KindIsEq <$> annotated kind <*> reservedSym "=" *> annotated kind) <|>
  internal (_KindIsPlain <$> reservedCon "Plain" *> annotated kind) <|>
  internal (_KindIsSub <$> annotated kind <*> reservedSym "≤" *> annotated kind) <|>
  expected "kind constraint"

program :: Syntax f => f Program
program = _Program <$> block (annotated decl) <|> expected "program"

decl :: Syntax f => f Decl
decl =
  _DeclRec <$> reservedId "rec" *> blockOrLine (annotated declRec) <|>
  declSyn <|>
  declOp <|>
  _DeclTerm <$> annotated declTerm <|>
  _DeclType <$> annotated declType <|>
  expected "declaration"

declRec :: Syntax f => f DeclRec
declRec =
  _DeclRecTerm <$> annotated declTerm <|>
  _DeclRecType <$> annotated declType <|>
  expected "recursive declaration"

declOp :: Syntax f => f Decl
declOp = _DeclOpSugar <$> reservedId "operator" *> annotated op <*> reservedSym "=" *> varId <*> annotated opRules

op :: Syntax f => f Op
op = _Op <$> special '(' *> atLeast 2 atom <* special ')' <|> expected "operator section"  where
  atom = _Nothing <$> special '_' <|> _Just <$> varSym <|> expected "operator or hole"

opRules :: Syntax f => f OpRules
opRules = _OpRules <$> blockLike (reservedId "where") (_Left <$> assoc <|> _Right <$> precs) <|> expected "operator rules"

assoc :: Syntax f => f Assoc
assoc = assoc' <* contextualId "associative" where
  assoc' =
    _AssocLeft <$> contextualId "left" <|>
    _AssocRight <$> contextualId "right"

precs :: Syntax f => f [Prec]
precs = blockLike (contextualId "precedence") prec

prec :: Syntax f => f Prec
prec = _Prec <$> ordering <*> op where
  ordering =
    _GT <$> contextualId "above" <|>
    _LT <$> contextualId "below" <|>
    _EQ <$> contextualId "equal"

declSyn :: Syntax f => f Decl
declSyn = _DeclSynSugar <$> reservedId "using" *> conId <*> reservedSym "=" *> annotated ty

declType :: Syntax f => f DeclType
declType = declTypeDataSugar <|> internal declTypeData <|> declTypeEnum where

  declTypeData :: Syntax f => f DeclType
  declTypeData = _DeclTypeData <$> reservedId "datatype" *> dataMode <*> conId <*> many (annotated typePat) <*> reservedSym "=" *> dataCons

  declTypeDataSugar :: Syntax f => f DeclType
  declTypeDataSugar = _DeclTypeDataSugar <$> reservedId "datatype" *> optional dataMode <*> conId <*> many (annotated typePat) <*> reservedSym "=" *> dataCons

  dataCons :: Syntax f => f [Annotated DataCon]
  dataCons = _Cons <$> annotated dataCon <*> many (contextualOp "|" *> annotated dataCon)

  dataMode :: Syntax f => f DataMode
  dataMode = (_DataBoxed <$> reservedId "boxed") <|> (_DataUnboxed <$> reservedId "unboxed")

  declTypeEnum :: Syntax f => f DeclType
  declTypeEnum = _DeclTypeEnum <$> reservedId "enum" *> conId <*> reservedSym "=" *> alts where
    alts = _Cons <$> conId <*> many (contextualOp "|" *> conId)


dataCon :: Syntax f => f DataCon
dataCon = _DataCon <$> conId <*> annotated ty1

typePat :: Syntax f => f TypePat
typePat = _TypePatVar <$> flavoredVarId <|>
          expected "type variable"

declTerm :: Syntax f => f DeclTerm
declTerm = prefix varId (_DeclTermSigSugar, declTermSig) (_DeclTermDefSugar, declTermDef) <|> internal declTermVar <|> expected "term declaration" where
  declTermSig = reservedSym ":" *> annotated qTy
  declTermDef = annotated pat `until` reservedSym "=" <*> annotated exp
  declTermVar = _DeclTermVar <$> varId <*> (_Just <$> reservedSym ":" *> annotated qTy) <*> reservedSym "=" *> annotated exp

bind :: Syntax f => f Bind
bind = _Bind <$> annotated pat <*> reservedSym "=" *> annotated exp <|> expected "binding"

pat :: Syntax f => f Pat
pat = prefix' conId (_PatData, annotated pat0) _PatEnum <|> pat0 <|> expected "pattern" where
  pat0 =
    _PatHole <$> special '_' <|>
    _PatLit <$> litNoString <|> -- TODO allow string literals
    prefix' varId (_PatAt, reservedSym "@" *> annotated pat) _PatVar <|>
    tuple _PatUnit _PatPair pat <|>
    expected "pattern(0)"

kind :: Syntax f => f Kind
kind = kind0 `join` (_KindFn, reservedSym "->" *> annotated kind) <|> expected "kind" where
  kind0 =
    _KindRef <$> reservedCon "Ref" <|>
    _KindType <$> reservedCon "Type" <|>
    _KindView <$> reservedCon "View" <|>
    internal (_KindUni <$> uni) <|>
    _KindConstraint <$> reservedCon "Constraint" <|>
    expected "kind(0)"

qTy :: Syntax f => f QType
qTy = poly <|> mono <|> expected "quantified type" where
  poly = _Forall <$> reservedId "forall" *> some (annotated typePat) <*> typeConstraints <*> (contextualOp "." *> annotated ty)
  mono = _Mono <$> annotated ty
  typeConstraints :: Syntax f => f [Annotated TypeConstraint]
  typeConstraints = _Cons <$> (contextualOp "|" *> annotated typeConstraint) <*> many (special ',' *> annotated typeConstraint) <|> _Nil <$> pure ()

ty :: Syntax f => f Type
ty = ty1 `join` (_TypeFn, reservedSym "->" *> annotated ty) <|> expected "type"

-- special sauce to make op applications right associative, but normal applications left associative
-- &r ?v C t &r ?v t -> &r (?v ((((C t) &r) ?v) t))
foldTy :: Prism Type [Annotated Type]
foldTy = Prism (view value . fold) (Just . unfold . phantom) where
  fold [x] = x
  fold (x:xs)
    | isTypeOp x  = let y = fold xs in (view source x <> view source y, Nothing) :< TypeApplyOp x y
    | otherwise = foldLeft (x:xs)
  foldLeft [x] = x
  foldLeft (x:y:ys) = fold ((view source x <> view source y, Nothing) :< TypeApply x y : ys)
  unfold x = case view value x of
    TypeApplyOp x y -> x : unfold y
    TypeApply _   _ -> unfoldLeft x
    _               -> [x]
  unfoldLeft x = case view value x of
    TypeApply x y -> unfoldLeft x ++ [y]
    _             -> [x]
  isTypeOp :: Annotated Type -> Bool
  isTypeOp t = case view value t of
    TypeIdentityOp -> True
    TypeRef _      -> True
    TypeSetOp _    -> True
    TypeUni Ref _  -> True
    TypeUni View _ -> True
    TypeVar Ref _  -> True
    TypeVar View _ -> True
    _              -> False

ty1 :: Syntax f => f Type
ty1 = foldTy <$> some (annotated ty0) <|> expected "type(1)" where
  ty0 =
    _TypeCon <$> conId <|>
    _TypeIdentityOp <$> reservedSym "@" <|>
    internal (_TypeRef <$> varIdRef) <|>
    _TypeSetOp <$> (Prism Set.fromList (Just . Set.toList) <$> (special '{' *> (_Cons <$> annotated ty <*> some (special ',' *> annotated ty)) <* special '}')) <|>
    internal (_TypeUni <$> flavoredUni) <|>
    _TypeVar <$> flavoredVarId <|>
    tuple _TypeUnit _TypePair ty <|>
    expected "type(0)"

tok :: Syntax f => f Tok
tok = internal (_TokOp <$> varSym <|> _TokExp <$> annotated exp) <|> expected "token"

exp :: Syntax f => f Exp
exp = exp6 `join` (_Sig, reservedSym ":" *> annotated ty) <|> expected "expression" where
  exp6 = optWhere <$> annotated exp5 <*> blockLike (reservedId "where") (annotated declTerm) <|> internal exp5 <|> expected "expression(6)"
  optWhere = Prism (\(e, ps) -> case ps of { [] -> view value e; _ -> Where e ps }) (\case { Where e ps -> Just (e, ps); _ -> Nothing })
  exp5 = rightWithSep (reservedId "defer") _Defer exp4 <|> expected "expression(5)"
  exp4 = rightWithSep (reservedId "seq") _Seq exp3 <|> expected "expression(4)"
  exp3 =
    _Read <$> reservedId "read" *> varId <*> reservedId "in" *> annotated exp <|>
    _DoSugar <$> reservedId "do" *> block (annotated stmt) <|>
    _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
    _Cases <$> reservedId "cases" *> block alt <|>
    _If <$> reservedId "if" *> annotated exp <*> reservedId "then" *> annotated exp <*> reservedId "else" *> annotated exp <|>
    _Lambda <$> reservedSym "\\" *> alt <|>
    internal (_Capture <$> empty <*> annotated exp3) <|>
    _Let <$> reservedId "let" *> annotated bind <*> reservedId "in" *> annotated exp <|>
    _Switch <$> reservedId "switch" *> block switch <|>
    exp2 <|> expected "expression(3)"
  exp2 = mixfix <$> some (annotated (_TokOp <$> varSym <|> _TokExp <$> annotated exp1)) <|> internal exp1 <|> expected "expression(2)"
  mixfix = Prism (\ts -> case ts of { [_ :< TokExp e] -> view value e; _ -> MixfixSugar ts }) (\case { MixfixSugar ts -> Just ts; _ -> Nothing })
  exp1 = left _Apply exp0 <|> expected "expression(1)"
  exp0 =
    _VarRefSugar <$> varIdRef <|>
    _Var <$> varId <|>
    _Con <$> conId <|>
    _Lit <$> lit <|>
    internal (_Specialize <$> annotated exp0 <*> empty) <|>
    tuple _Unit _Pair exp <|> -- Note: Grouping parentheses are handled here
    expected "expression(0)"

switch :: Syntax f => f (Annotated Exp, Annotated Exp)
switch = annotated exp <*> reservedSym "->" *> annotated exp <|> expected "switch alternative"

-- TODO allow "let ... in" in expression?
stmt :: Syntax f => f Stmt
stmt = _StmtBind <$> reservedId "let" *> annotated bind <|> _StmtExp <$> annotated exp <|> expected "statement"

alt :: Syntax f => f (Annotated Pat, Annotated Exp)
alt = annotated pat <*> reservedSym "->" *> annotated exp <|> expected "case alternative"

typeRequirement :: Syntax f => f TypeRequirement
typeRequirement = _Requirement <$> typeConstraint

kindRequirement :: Syntax f => f KindRequirement
kindRequirement = _Requirement <$> kindConstraint
