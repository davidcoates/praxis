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
special c = token (Special c) <|> mark ("special '" ++ [c] ++ "'")

layout :: Syntax f => Char -> f ()
layout c = token (Layout c) <|> mark ("layout '" ++ [c] ++ "'")

contextualOp :: Syntax f => Name -> f ()
contextualOp op = token (VarSym op) <|> internal (reservedSym op) <|> mark ("contextual keyword '" ++ op ++ "'")

contextualId :: Syntax f => Name -> f ()
contextualId id = token (VarId id) <|> internal (reservedId id) <|> mark ("contextual keyword '" ++ id ++ "'")

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
typeConstraint = _TypeIsInstance <$> annotated ty <|>
                 internal (_TypeIsEq <$> annotated ty <*> reservedSym "=" *> annotated ty) <|>
                 internal (_TypeIsEqIfAffine <$> annotated ty <*> reservedSym "=" *> annotated ty <*> reservedSym "|" *> annotated ty) <|>
                 internal (_TypeIsIntegralOver <$> swap <$> integer <*> reservedSym "∈" *> annotated ty) <|>
                 internal (_TypeIsRef <$> reservedCon "Ref" *> annotated ty) <|>
                 internal (_TypeIsRefFree <$> swap <$> varId <*> reservedSym "∉" *> annotated ty) <|>
                 internal (_TypeIsSub <$> annotated ty <*> reservedSym "≤" *> annotated ty) <|>
                 internal (_TypeIsSubIfAffine <$> annotated ty <*> reservedSym "≤" *> annotated ty <*> reservedSym "|" *> annotated ty) <|>
                 internal (_TypeIsValue <$> reservedCon "Value" *> annotated ty) <|>
                 mark "type constraint"

kindConstraint :: Syntax f => f KindConstraint
kindConstraint = internal (_KindIsEq <$> annotated kind <*> reservedSym "=" *> annotated kind) <|>
                 internal (_KindIsPlain <$> reservedCon "Plain" *> annotated kind) <|>
                 internal (_KindIsSub <$> annotated kind <*> reservedSym "≤" *> annotated kind) <|>
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
declTypeData = _DeclTypeData <$> reservedId "datatype" *> dataMode <*> conId <*> many (annotated typePat) <*> reservedSym "=" *> dataCons where
  dataCons = _Cons <$> annotated dataCon <*> many (contextualOp "|" *> annotated dataCon)
  dataMode = (_DataBoxed <$> reservedId "boxed") <|> (_DataRec <$> reservedId "rec") <|> (_DataUnboxed <$> (reservedId "unboxed" <|> pure ()))

declTypeEnum :: Syntax f => f DeclType
declTypeEnum = _DeclTypeEnum <$> reservedId "enum" *> conId <*> reservedSym "=" *> alts where
  alts = _Cons <$> conId <*> many (contextualOp "|" *> conId)

dataCon :: Syntax f => f DataCon
dataCon = _DataCon <$> conId <*> annotated ty1

typePat :: Syntax f => f TypePat
typePat = _TypePatVar <$> flavoredVarId <|>
          mark "type variable"

declTerm :: Syntax f => f DeclTerm
declTerm = declTermRec <|> declTerm' <|> mark "term declaration/definition" where
  declTerm' = prefix varId (_DeclTermSigSweet, declTermSig) (_DeclTermDefSweet, declTermDef) <|> internal declTermVar <|> mark "non-rec term declaration/definition"
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
         prefix' varId (_PatAt, reservedSym "@" *> annotated pat) _PatVar <|>
         tuple _PatUnit _PatPair pat <|>
         mark "pattern(0)"

kind :: Syntax f => f Kind
kind = kind0 `join` (_KindFn, reservedSym "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindRef <$> reservedCon "Ref" <|>
          _KindType <$> reservedCon "Type" <|>
          _KindView <$> reservedCon "View" <|>
          internal (_KindUni <$> uni) <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          mark "kind(0)"

qTy :: Syntax f => f QType
qTy = poly <|> mono <|> mark "quantified type" where
  poly = _Forall <$> reservedId "forall" *> some (annotated typePat) <*> typeConstraints <*> (contextualOp "." *> annotated ty)
  mono = _Mono <$> annotated ty
  typeConstraints :: Syntax f => f [Annotated TypeConstraint]
  typeConstraints = _Cons <$> (contextualOp "|" *> annotated typeConstraint) <*> many (special ',' *> annotated typeConstraint) <|> _Nil <$> pure ()

ty :: Syntax f => f Type
ty = ty1 `join` (_TypeFn, reservedSym "->" *> annotated ty) <|> mark "type"

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
ty1 = foldTy <$> some (annotated ty0) <|> mark "type(1)" where
  ty0 = _TypeCon <$> conId <|>
        _TypeIdentityOp <$> reservedSym "@" <|>
        internal (_TypeRef <$> varIdRef) <|>
        _TypeSetOp <$> (Prism Set.fromList (Just . Set.toList) <$> (special '{' *> (_Cons <$> annotated ty <*> some (special ',' *> annotated ty)) <* special '}')) <|>
        internal (_TypeUni <$> flavoredUni) <|>
        _TypeVar <$> flavoredVarId <|>
        tuple _TypeUnit _TypePair ty <|>
        mark "type(0)"

tok :: Syntax f => f Tok
tok = internal (_TokOp <$> varSym <|> _TokExp <$> annotated exp) <|> mark "token"

exp :: Syntax f => f Exp
exp = exp6 `join` (_Sig, reservedSym ":" *> annotated ty) <|> mark "expression" where
  exp6 = optWhere <$> annotated exp5 <*> blockLike (reservedId "where") (annotated declTerm) <|> internal exp5 <|> mark "expression(6)"
  optWhere = Prism (\(e, ps) -> case ps of { [] -> view value e; _ -> Where e ps }) (\case { Where e ps -> Just (e, ps); _ -> Nothing })
  exp5 = rightWithSep (reservedId "defer") _Defer exp4 <|> mark "expression(5)"
  exp4 = rightWithSep (reservedId "seq") _Seq exp3 <|> mark "expression(4)"
  exp3 = _Read <$> reservedId "read" *> varId <*> reservedId "in" *> annotated exp <|>
         _DoSweet <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         _If <$> reservedId "if" *> annotated exp <*> reservedId "then" *> annotated exp <*> reservedId "else" *> annotated exp <|>
         _Lambda <$> reservedSym "\\" *> alt <|>
         internal (_Closure <$> empty <*> annotated exp3) <|>
         _Let <$> reservedId "let" *> annotated bind <*> reservedId "in" *> annotated exp <|>
         _Switch <$> reservedId "switch" *> block switch <|>
         exp2 <|> mark "expression(3)"
  exp2 = mixfix <$> some (annotated (_TokOp <$> varSym <|> _TokExp <$> annotated exp1)) <|> internal exp1 <|> mark "expression(2)"
  mixfix = Prism (\ts -> case ts of { [_ :< TokExp e] -> view value e; _ -> MixfixSweet ts }) (\case { MixfixSweet ts -> Just ts; _ -> Nothing })
  exp1 = left _Apply exp0 <|> mark "expression(1)"
  exp0 = _VarRefSweet <$> varIdRef <|>
         _Var <$> varId <|>
         _Con <$> conId <|>
         _Lit <$> lit <|>
         internal (_Specialise <$> annotated exp0 <*> empty) <|>
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
op = _Op <$> special '(' *> atLeast 2 atom <* special ')' <|> mark "operator section"  where
  atom = _Nothing <$> special '_' <|> _Just <$> varSym <|> mark "operator or hole"

opRules :: Syntax f => f OpRules
opRules = _OpRulesSweet <$> blockLike (reservedId "where") (_Left <$> annotated assoc <|> _Right <$> precs) <|>
          internal (Prism undefined (\r -> case r of { OpRules Nothing [] -> Just (); _ -> Nothing}) <$> pure ()) <|> -- TODO tidy up
          internal (_OpRules <$> reservedId "where" *> layout '{' *> optional (annotated assoc <* layout ';') <*> precs <* layout '}')

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

typeRequirement :: Syntax f => f TypeRequirement
typeRequirement = _Requirement <$> typeConstraint

kindRequirement :: Syntax f => f KindRequirement
kindRequirement = _Requirement <$> kindConstraint
