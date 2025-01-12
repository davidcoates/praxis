{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}


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
syntax :: (Syntax f, IsTerm a, IsStage s) => TermT a -> f (a s)
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


tuple :: (Syntax f, IsTerm a, IsStage s) => Prism (a s) () -> Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
tuple unit pair p = special '(' *> tuple' where
  tuple' = unit <$> special ')' *> pure () <|> rightWithSep (special ',') pair p <* special ')'

join :: (Syntax f, IsTerm a, IsStage s) => f (a s) -> (Prism (a s) (Annotated s a, b), f b) -> f (a s)
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> internal p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

right :: (Syntax f, IsTerm a, IsStage s) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
right = rightWithSep (pure ())

left :: (Syntax f, IsTerm a, IsStage s) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
left = leftWithSep (pure ())

blank :: forall a s. StageT s -> TermT a -> Annotation s a
blank stage _ = case stage of
  InitialT -> ()

foldRight :: forall a s. (IsTerm a, IsStage s) => Prism (a s) (Annotated s a, Annotated s a) -> Prism (Annotated s a) [Annotated s a]
foldRight _P = Prism fold (Just . unfold) where
  fold [x]    = x
  fold (x:xs) = let y = fold xs in (view source x <> view source y, blank (stageT :: StageT s) (termT :: TermT a)) :< construct _P (x, y)
  unfold x = case destruct _P (view value x) of
    Just (x, y) -> x : unfold y
    Nothing     -> [x]

foldLeft :: forall a s. (IsTerm a, IsStage s) => Prism (a s) (Annotated s a, Annotated s a) -> Prism (Annotated s a) [Annotated s a]
foldLeft _P = Prism fold (Just . unfold) where
  fold [x]      = x
  fold (x:y:ys) = fold ((view source x <> view source y, blank (stageT :: StageT s) (termT :: TermT a)) :< construct _P (x, y) : ys)
  unfold x = case destruct _P (view value x) of
    Just (x, y) -> unfold x ++ [y]
    Nothing     -> [x]

rightWithSep :: (Syntax f, IsTerm a, IsStage s) => f () -> Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
rightWithSep s _P p = unannotated $ foldRight _P <$> (_Cons <$> annotated p <*> many (s *> annotated p))

leftWithSep :: (Syntax f, IsTerm a, IsStage s) => f () -> Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
leftWithSep s _P p = unannotated $ foldLeft _P <$> (_Cons <$> annotated p <*> many (s *> annotated p))

integer :: Syntax f => f Integer
integer = match f (Token.Lit . Integer) where
  f = \case
    Token.Lit (Integer n) -> Just n
    _                     -> Nothing

typeConstraint :: (Syntax f, IsStage s) => f (TypeConstraint s)
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

kindConstraint :: (Syntax f, IsStage s) => f (KindConstraint s)
kindConstraint =
  internal (_KindIsEq <$> annotated kind <*> reservedSym "=" *> annotated kind) <|>
  internal (_KindIsPlain <$> reservedCon "Plain" *> annotated kind) <|>
  internal (_KindIsSub <$> annotated kind <*> reservedSym "≤" *> annotated kind) <|>
  expected "kind constraint"

program :: (Syntax f, IsStage s) => f (Program s)
program = _Program <$> block (annotated decl) <|> expected "program"

decl :: (Syntax f, IsStage s) => f (Decl s)
decl =
  _DeclRec <$> reservedId "rec" *> blockOrLine (annotated declRec) <|>
  declSyn <|>
  declOp <|>
  _DeclTerm <$> annotated declTerm <|>
  _DeclType <$> annotated declType <|>
  expected "declaration"

declRec :: (Syntax f, IsStage s) => f (DeclRec s)
declRec =
  _DeclRecTerm <$> annotated declTerm <|>
  _DeclRecType <$> annotated declType <|>
  expected "recursive declaration"

declOp :: (Syntax f, IsStage s) => f (Decl s)
declOp = _DeclOpSugar <$> reservedId "operator" *> annotated op <*> reservedSym "=" *> varId <*> annotated opRules

op :: (Syntax f, IsStage s) => f (Op s)
op = _Op <$> special '(' *> atLeast 2 atom <* special ')' <|> expected "operator section"  where
  atom = _Nothing <$> special '_' <|> _Just <$> varSym <|> expected "operator or hole"

opRules :: (Syntax f, IsStage s) => f (OpRules s)
opRules = _OpRules <$> blockLike (reservedId "where") (_Left <$> assoc <|> _Right <$> precs) <|> expected "operator rules"

assoc :: Syntax f => f Assoc
assoc = assoc' <* contextualId "associative" where
  assoc' =
    _AssocLeft <$> contextualId "left" <|>
    _AssocRight <$> contextualId "right"

precs :: (Syntax f, IsStage s) => f [Annotated s Prec]
precs = blockLike (contextualId "precedence") (annotated prec)

prec :: (Syntax f, IsStage s) => f (Prec s)
prec = _Prec <$> ordering <*> annotated op where
  ordering =
    _GT <$> contextualId "above" <|>
    _LT <$> contextualId "below" <|>
    _EQ <$> contextualId "equal"

declSyn :: (Syntax f, IsStage s) => f (Decl s)
declSyn = _DeclSynSugar <$> reservedId "using" *> conId <*> reservedSym "=" *> annotated ty

declType :: (Syntax f, IsStage s) => f (DeclType s)
declType = declTypeDataSugar <|> internal declTypeData <|> declTypeEnum where

  declTypeData :: (Syntax f, IsStage s) => f (DeclType s)
  declTypeData = _DeclTypeData <$> reservedId "datatype" *> dataMode <*> conId <*> many (annotated typePat) <*> reservedSym "=" *> dataCons

  declTypeDataSugar :: (Syntax f, IsStage s) => f (DeclType s)
  declTypeDataSugar = _DeclTypeDataSugar <$> reservedId "datatype" *> optional dataMode <*> conId <*> many (annotated typePat) <*> reservedSym "=" *> dataCons

  dataCons :: (Syntax f, IsStage s) => f [Annotated s DataCon]
  dataCons = _Cons <$> annotated dataCon <*> many (contextualOp "|" *> annotated dataCon)

  dataMode :: Syntax f => f DataMode
  dataMode = (_DataBoxed <$> reservedId "boxed") <|> (_DataUnboxed <$> reservedId "unboxed")

  declTypeEnum :: (Syntax f, IsStage s) => f (DeclType s)
  declTypeEnum = _DeclTypeEnum <$> reservedId "enum" *> conId <*> reservedSym "=" *> alts where
    alts = _Cons <$> conId <*> many (contextualOp "|" *> conId)


dataCon :: (Syntax f, IsStage s) => f (DataCon s)
dataCon = _DataCon <$> conId <*> annotated ty1

typePat :: (Syntax f, IsStage s) => f (TypePat s)
typePat =
  _TypePatVar <$> flavoredVarId <|>
  expected "type variable"

declTerm :: (Syntax f, IsStage s) => f (DeclTerm s)
declTerm = prefix varId (_DeclTermSigSugar, declTermSig) (_DeclTermDefSugar, declTermDef) <|> internal declTermVar <|> expected "term declaration" where
  declTermSig = reservedSym ":" *> annotated qTy
  declTermDef = annotated pat `until` reservedSym "=" <*> annotated exp
  declTermVar = _DeclTermVar <$> varId <*> (_Just <$> reservedSym ":" *> annotated qTy) <*> reservedSym "=" *> annotated exp

bind :: (Syntax f, IsStage s) => f (Bind s)
bind = _Bind <$> annotated pat <*> reservedSym "=" *> annotated exp <|> expected "binding"

pat :: (Syntax f, IsStage s) => f (Pat s)
pat = prefix' conId (_PatData, annotated pat0) _PatEnum <|> pat0 <|> expected "pattern" where
  pat0 =
    _PatHole <$> special '_' <|>
    _PatLit <$> litNoString <|> -- TODO allow string literals
    prefix' varId (_PatAt, reservedSym "@" *> annotated pat) _PatVar <|>
    tuple _PatUnit _PatPair pat <|>
    expected "pattern(0)"

kind :: (Syntax f, IsStage s) => f (Kind s)
kind = kind0 `join` (_KindFn, reservedSym "->" *> annotated kind) <|> expected "kind" where
  kind0 =
    _KindRef <$> reservedCon "Ref" <|>
    _KindType <$> reservedCon "Type" <|>
    _KindView <$> reservedCon "View" <|>
    internal (_KindUni <$> uni) <|>
    _KindConstraint <$> reservedCon "Constraint" <|>
    expected "kind(0)"

qTy :: (Syntax f, IsStage s) => f (QType s)
qTy = poly <|> mono <|> expected "quantified type" where
  poly = _Forall <$> reservedId "forall" *> some (annotated typePat) <*> typeConstraints <*> (contextualOp "." *> annotated ty)
  mono = _Mono <$> annotated ty
  typeConstraints :: (Syntax f, IsStage s) => f [Annotated s TypeConstraint]
  typeConstraints = _Cons <$> (contextualOp "|" *> annotated typeConstraint) <*> many (special ',' *> annotated typeConstraint) <|> _Nil <$> pure ()

ty :: (Syntax f, IsStage s) => f (Type s)
ty = ty1 `join` (_TypeFn, reservedSym "->" *> annotated ty) <|> expected "type"

-- special sauce to make op applications right associative, but normal applications left associative e.g. &r ?v C t &r ?v t -> &r (?v ((((C t) &r) ?v) t))
foldType :: forall s. (IsStage s) => Prism (Annotated s Type) [Annotated s Type]
foldType = Prism fold (Just . unfold) where
  fold [x] = x
  fold (x:xs)
    | isTypeOp x = let y = fold xs in (view source x <> view source y, blank (stageT :: StageT s) TypeT) :< TypeApplyOp x y
    | otherwise = foldLeft (x:xs)
  foldLeft [x] = x
  foldLeft (x:y:ys) = fold ((view source x <> view source y, blank (stageT :: StageT s) TypeT) :< TypeApply x y : ys)
  unfold x = case view value x of
    TypeApplyOp x y -> x : unfold y
    TypeApply _ _   -> unfoldLeft x
    _               -> [x]
  unfoldLeft x = case view value x of
    TypeApply x y -> unfold x ++ [y]
    _             -> [x]

ty1 :: (Syntax f, IsStage s) => f (Type s)
ty1 = unannotated (foldType <$> some (annotated ty0)) <|> expected "type(1)" where
  ty0 =
    _TypeCon <$> conId <|>
    _TypeIdentityOp <$> reservedSym "@" <|>
    internal (_TypeRef <$> varIdRef) <|>
    _TypeSetOp <$> (Prism Set.fromList (Just . Set.toList) <$> (special '{' *> (_Cons <$> annotated ty <*> some (special ',' *> annotated ty)) <* special '}')) <|>
    internal (_TypeUni <$> flavoredUni) <|>
    _TypeVar <$> flavoredVarId <|>
    tuple _TypeUnit _TypePair ty <|>
    expected "type(0)"

tok :: (Syntax f, IsStage s) => f (Tok s)
tok = internal (_TokOp <$> varSym <|> _TokExp <$> annotated exp) <|> expected "token"

exp :: (Syntax f, IsStage s) => f (Exp s)
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

switch :: (Syntax f, IsStage s) => f (Annotated s Exp, Annotated s Exp)
switch = annotated exp <*> reservedSym "->" *> annotated exp <|> expected "switch alternative"

-- TODO allow "let ... in" in expression?
stmt :: (Syntax f, IsStage s) => f (Stmt s)
stmt = _StmtBind <$> reservedId "let" *> annotated bind <|> _StmtExp <$> annotated exp <|> expected "statement"

alt :: (Syntax f, IsStage s) => f (Annotated s Pat, Annotated s Exp)
alt = annotated pat <*> reservedSym "->" *> annotated exp <|> expected "case alternative"

typeRequirement :: (Syntax f, IsStage s) => f (Requirement TypeConstraint s)
typeRequirement = _Requirement <$> annotated typeConstraint

kindRequirement :: (Syntax f, IsStage s) => f (Requirement KindConstraint s)
kindRequirement = _Requirement <$> annotated kindConstraint
