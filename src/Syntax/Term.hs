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
import           Prelude       hiding (_Just, exp, pure, until, (*>), (<$>),
                                (<*), (<*>))

definePrisms ''Bool
definePrisms ''Ordering

until :: Syntax f => f a -> f () -> f [a]
until p q = _Nil <$> q <|> _Cons <$> p <*> until p q

token :: Syntax f => Token -> f ()
token t = match (\t' -> if t' == t then Just () else Nothing) (const t)

special :: Syntax f => Char -> f ()
special c = token (Special c) <|> mark ("special '" ++ [c] ++ "'")

layout :: Syntax f => Char -> f ()
layout c = token (Layout c) <|> mark ("layout '" ++ [c] ++ "'")

contextualOp :: Syntax f => Name -> f ()
contextualOp op = token (VarSym op) <|> unparseable (reservedSym op) <|> mark ("contextual keyword '" ++ op ++ "'")

contextualId :: Syntax f => Name -> f ()
contextualId id = token (VarId id) <|> unparseable (reservedId id) <|> mark ("contextual keyword '" ++ id ++ "'")

dot :: Syntax f => f ()
dot = contextualOp "."

block :: Syntax f => f a -> f [a]
block p = layout '{' *> _Cons <$> p <*> (layout ';' *> p) `until` layout '}'

blockOrLine :: Syntax f => f a -> f [a]
blockOrLine f = _Cons <$> layout '{' *> f <*> (layout ';' *> f) `until` layout '}' <|>
                _Cons <$> f <*> _Nil <$> pure ()

blockLike :: Syntax f => f () -> f a -> f [a]
blockLike f g = f *> blockOrLine g <|>
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

varSym :: Syntax f => f Name
varSym = match f VarSym where
  f = \case
    VarSym n -> Just n
    _        -> Nothing

uni :: Syntax f => f Name
uni = match (const Nothing) Uni

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
reservedSym s = token (ReservedSym s) <|> mark ("reserved symbol '" ++ s ++ "'")

reservedCon :: Syntax f => String -> f ()
reservedCon s = token (ReservedCon s) <|> mark ("reserved name '" ++ s ++ "'")

reservedId :: Syntax f => String -> f ()
reservedId s = token (ReservedId s) <|> mark ("reserved name '" ++ s ++ "'")

definePrisms ''Assoc
definePrisms ''Op
definePrisms ''OpRules
definePrisms ''Prec

definePrisms ''Bind
definePrisms ''DataCon
definePrisms ''DataMode
definePrisms ''Decl
definePrisms ''DeclTerm
definePrisms ''DeclType
definePrisms ''Exp
definePrisms ''Pat
definePrisms ''Program
definePrisms ''Stmt
definePrisms ''Tok

definePrisms ''ViewDomain
definePrisms ''View
definePrisms ''TyPat
definePrisms ''Type
definePrisms ''QType
definePrisms ''QTyVar

definePrisms ''Kind

definePrisms ''KindConstraint
definePrisms ''TyConstraint

definePrisms ''Requirement

-- | The syntax for a given term type.
syntax :: (Term a, Syntax f) => I a -> f a
syntax = \case
  -- | Operators
  IAssoc          -> assoc
  IOp             -> op
  IOpRules        -> opRules
  IPrec           -> prec
  -- | T0
  IDataCon        -> dataCon
  IDecl           -> decl
  IDeclTerm       -> declTerm
  IDeclType       -> declType
  IExp            -> exp
  IPat            -> pat
  IProgram        -> program
  IStmt           -> stmt
  ITok            -> undefined
  -- | T1
  IView           -> view'
  ITyPat          -> tyPat
  IType           -> ty
  ITyConstraint   -> tyConstraint
  IQType          -> qTy
  IQTyVar         -> qTyVar
  -- | T2
  IKind           -> kind
  IKindConstraint -> kindConstraint
  -- | Solver
  ITyRequirement   -> tyRequirement
  IKindRequirement -> kindRequirement


tuple :: (Syntax f, Term a) => Prism a () -> Prism a (Annotated a, Annotated a) -> f a -> f a
tuple unit pair p = special '(' *> tuple' where
  tuple' = unit <$> special ')' *> pure () <|> rightWithSep (special ',') pair p <* special ')'

tuple1 :: (Syntax f, Term a) => Prism a (Annotated a, Annotated a) -> f a -> f a
tuple1 pair p = special '(' *> rightWithSep (special ',') pair p <* special ')'

-- at least 2 elements
pack :: (Syntax f, Term a) => Prism a (Annotated a, Annotated a) -> f a -> f a
pack pair p = pair <$> (contextualOp "[" *> annotated p <* special ',') <*> (annotated (rightWithSep (special ',') pair p) <* contextualOp "]")

join :: (Syntax f, Term a) => f a -> (Prism a (Annotated a, b), f b) -> f a
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> unparseable p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

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

tyConstraint :: Syntax f => f TyConstraint
tyConstraint = unparseable (_HoldsInteger <$> integer <*> reservedSym "∈" *> annotated ty) <|>
               _Instance <$> annotated ty <|>
               unparseable (_RefFree <$> varId <*> reservedId "ref-free" *> annotated ty) <|>
               unparseable (_TEq <$> annotated ty <*> reservedSym "=" *> annotated ty) <|>
               unparseable (_TOpEq <$> annotated ty <*> reservedSym "?=" *> annotated ty) <|>
               mark "type constraint"

kindConstraint :: Syntax f => f KindConstraint
kindConstraint = unparseable (_KEq <$> annotated kind <*> reservedSym "=" *> annotated kind) <|>
                 unparseable (_KSub <$> annotated kind <*> reservedSym "≤" *> annotated kind) <|>
                 mark "kind constraint"

program :: Syntax f => f Program
program = _Program <$> block (annotated decl) -- TODO module

decl :: Syntax f => f Decl
decl = declSyn <|> (_DeclType <$> annotated declType) <|> declOp <|> (_DeclTerm <$> annotated declTerm) -- TODO imports

declSyn :: Syntax f => f Decl
declSyn = _DeclSynSweet <$> reservedId "using" *> conId <*> reservedSym "=" *> annotated ty

declType :: Syntax f => f DeclType
declType = declTypeData <|> declTypeEnum

declTypeData :: Syntax f => f DeclType
declTypeData = _DeclTypeData <$> reservedId "datatype" *> dataMode <*> conId <*> optional (annotated tyPat) <*> reservedSym "=" *> dataCons where
  dataCons = _Cons <$> annotated dataCon <*> many (contextualOp "|" *> annotated dataCon)
  dataMode = (_DataBoxed <$> reservedId "boxed") <|> (_DataRec <$> reservedId "rec") <|> (_DataUnboxed <$> (reservedId "unboxed" <|> pure ()))

declTypeEnum :: Syntax f => f DeclType
declTypeEnum = _DeclTypeEnum <$> reservedId "enum" *> conId <*> reservedSym "=" *> alts where
  alts = _Cons <$> conId <*> many (contextualOp "|" *> conId)

dataCon :: Syntax f => f DataCon
dataCon = _DataCon <$> conId <*> annotated ty1

tyPat :: Syntax f => f TyPat
tyPat = tyPat0 <|> pack _TyPatPack tyPat0 <|> mark "type pattern" where
  tyPat0 = _TyPatVar <$> varId <|>
           _TyPatViewVar <$> viewDomain <*> varId <|>
           unparseable (pack _TyPatPack tyPat) <|>
           mark "type pattern(0)"

declTerm :: Syntax f => f DeclTerm
declTerm = declTermRec <|> declTerm' <|> mark "term declaration/definition" where
  declTerm' = prefix varId (_DeclTermSigSweet, declTermSig) (_DeclTermDefSweet, declTermDef) <|> unparseable declTermVar <|> mark "non-rec term declaration/definition"
  declTermSig = reservedSym ":" *> annotated qTy
  declTermDef = annotated pat `until` reservedSym "=" <*> annotated exp
  declTermVar = _DeclTermVar <$> varId <*> (_Just <$> reservedSym ":" *> annotated qTy) <*> reservedSym "=" *> annotated exp
  declTermRec = _DeclTermRec <$> reservedId "rec" *> blockOrLine (annotated declTerm')

bind :: Syntax f => f Bind
bind = _Bind <$> annotated pat <*> reservedSym "=" *> annotated exp <|> mark "binding"

pat :: Syntax f => f Pat
pat = prefix' conId (_PatData, annotated pat0) _PatEnum <|> pat0 <|> mark "pattern" where
  pat0 = _PatHole <$> special '_' <|>
         _PatLit <$> litNoString <|> -- TODO allow string literals
         _PatVar <$> varId <|>
         tuple _PatUnit _PatPair pat <|>
         mark "pattern(0)"

kind :: Syntax f => f Kind
kind = kind0 `join` (_KindFn, reservedSym "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindView <$> reservedCon "View" *> viewDomain <|>
          _KindType <$> reservedCon "Type" <|>
          unparseable (_KindUni <$> uni) <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          tuple1 _KindPair kind <|>
          mark "kind(0)"

qTy :: Syntax f => f QType
qTy = poly <|> mono <|> mark "quantified type" where
  poly = _Forall <$> reservedId "forall" *> some (annotated qTyVar) <*> tyConstraints <*> (dot *> annotated ty)
  mono = _Mono <$> annotated ty
  tyConstraints :: Syntax f => f [Annotated TyConstraint]
  tyConstraints = _Cons <$> (contextualOp "|" *> annotated tyConstraint) <*> many (special ',' *> annotated tyConstraint) <|> _Nil <$> pure ()

qTyVar :: Syntax f => f QTyVar
qTyVar = _QTyVar <$> varId <|>
         _QViewVar <$> viewDomain <*> varId <|>
          mark "type variable"

ty :: Syntax f => f Type
ty = ty1 `join` (_TyFn, reservedSym "->" *> annotated ty) <|> mark "type"

viewDomain :: Syntax f => f ViewDomain
viewDomain = _Ref <$> reservedSym "&" <|>
             _RefOrValue <$> reservedSym "?" <|>
             mark "view domain"

ty1 :: Syntax f => f Type
ty1 = left _TyApply ty0 <|> mark "type(1)" where
  ty0 = _TyView  <$> annotated view' <|>
        _TyVar <$> varId <|>
        _TyCon <$> conId <|>
        unparseable (_TyUni <$> uni) <|>
        pack _TyPack ty <|>
        tuple _TyUnit _TyPair ty <|>
        mark "type(0)"

view' :: Syntax f => f View
view' = unparseable (_ViewUni <$> viewDomain <*> uni) <|>
        unparseable (_ViewRef <$> reservedSym "&" *> varId) <|>
        unparseable (_ViewValue <$> contextualId "«value-view»") <|>
        _ViewVar <$> viewDomain <*> varId <|>
        mark "view"

exp :: Syntax f => f Exp
exp = exp6 `join` (_Sig, reservedSym ":" *> annotated ty) <|> mark "expression" where
  exp6 = optWhere <$> annotated exp5 <*> blockLike (reservedId "where") (annotated declTerm) <|> unparseable exp5 <|> mark "expression(6)"
  optWhere = Prism (\(e, ps) -> case ps of { [] -> view value e; _ -> Where e ps }) (\case { Where e ps -> Just (e, ps); _ -> Nothing })
  exp5 = rightWithSep (reservedId "defer") _Defer exp4 <|> mark "expression(5)"
  exp4 = rightWithSep (reservedId "seq") _Seq exp3 <|> mark "expression(4)"
  exp3 = _Read <$> reservedId "read" *> varId <*> reservedId "in" *> annotated exp <|>
         _DoSweet <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         _If <$> reservedId "if" *> annotated exp <*> reservedId "then" *> annotated exp <*> reservedId "else" *> annotated exp <|>
         _Lambda <$> reservedSym "\\" *> alt <|>
         unparseable (_Closure <$> empty <*> annotated exp3) <|>
         _Let <$> reservedId "let" *> annotated bind <*> reservedId "in" *> annotated exp <|>
         _Switch <$> reservedId "switch" *> block switch <|>
         exp2 <|> mark "expression(3)"
  exp2 = mixfix <$> some (annotated (_TOp <$> varSym <|> _TExp <$> annotated exp1)) <|> unparseable exp1 <|> mark "expression(2)"
  mixfix = Prism (\ts -> case ts of { [_ :< TExp e] -> view value e; _ -> MixfixSweet ts }) (\case { MixfixSweet ts -> Just ts; _ -> Nothing })
  exp1 = left _Apply exp0 <|> mark "expression(1)"
  exp0 = _VarRefSweet <$> reservedSym "&" *> varId <|>
         _Var <$> varId <|>
         _Con <$> conId <|>
         _Lit <$> lit <|>
         unparseable (_Specialise <$> annotated exp0 <*> empty) <|>
         tuple _Unit _Pair exp <|> -- Note: Grouping parentheses are handled here
         mark "expression(0)"

switch :: Syntax f => f (Annotated Exp, Annotated Exp)
switch = annotated exp <*> reservedSym "->" *> annotated exp <|> mark "switch alternative"

-- TODO allow "let ... in" in expression?
stmt :: Syntax f => f Stmt
stmt = _StmtBind <$> reservedId "let" *> annotated bind <|> _StmtExp <$> annotated exp <|> mark "statement"

alt :: Syntax f => f (Annotated Pat, Annotated Exp)
alt = annotated pat <*> reservedSym "->" *> annotated exp <|> mark "case alternative"

declOp :: Syntax f => f Decl
declOp = _DeclOpSweet <$> reservedId "operator" *> annotated op <*> reservedSym "=" *> varId <*> annotated opRules

op :: Syntax f => f Op
op = _Op <$> special '(' *> atLeast 2 atom <* special ')' where
  atom = _Nothing <$> special '_' <|> _Just <$> varSym

opRules :: Syntax f => f OpRules
opRules = _OpRulesSweet <$> blockLike (reservedId "where") (_Left <$> annotated assoc <|> _Right <$> precs) <|>
          unparseable (Prism undefined (\r -> case r of { OpRules Nothing [] -> Just (); _ -> Nothing}) <$> pure ()) <|> -- TODO tidy up
          unparseable (_OpRules <$> reservedId "where" *> layout '{' *> optional (annotated assoc <* layout ';') <*> precs <* layout '}')

assoc :: Syntax f => f Assoc
assoc = assoc' <* contextualId "associative" where
  assoc' = _AssocLeft <$> contextualId "left" <|>
           _AssocRight <$> contextualId "right"

precs :: Syntax f => f [Annotated Prec]
precs = blockLike (contextualId "precedence") (annotated prec)

prec :: Syntax f => f Prec
prec = _Prec <$> ordering <*> op where
  ordering = _GT <$> contextualId "above" <|>
             _LT <$> contextualId "below" <|>
             _EQ <$> contextualId "equal"

tyRequirement :: Syntax f => f TyRequirement
tyRequirement = _Requirement <$> tyConstraint

kindRequirement :: Syntax f => f KindRequirement
kindRequirement = _Requirement <$> kindConstraint
