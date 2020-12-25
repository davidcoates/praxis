{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

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
import           Prelude       hiding (exp, pure, until, (*>), (<$>), (<*),
                                (<*>), _Just)

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

-- FIXME contextule reservation is dirty
contextualOp :: Syntax f => Name -> f ()
contextualOp op = token (QVarSym (unqualified op)) <|> mark ("contextually-reserved '" ++ op ++ "'")

contextualId :: Syntax f => Name -> f ()
contextualId id = token (QVarId (unqualified id)) <|> mark ("contextually-reserved '" ++ id ++ "'")

dot :: Syntax f => f ()
dot = contextualOp "."

block :: Syntax f => f a -> f [a]
block p = layout '{' *> _Cons <$> p <*> (layout ';' *> p) `until` layout '}'

blockOrLine :: Syntax f => f a -> f (a, [a])
blockOrLine f = layout '{' *> f <*> (layout ';' *> f) `until` layout '}' <|>
                f <*> _Nil <$> pure ()

blockLike :: Syntax f => f () -> f a -> f [a]
blockLike f g = _Cons <$> f *> blockOrLine g <|>
                _Nil <$> pure ()

varid :: Syntax f => f String
varid = match f (\s -> QVarId (unqualified s)) where
  f = \case
    QVarId n -> if null (qualification n) then Just (unqualify n) else Nothing
    _        -> Nothing

tyOpVar :: Syntax f => f String
tyOpVar = match f (\s -> Token.TyOpVar s) where
  f = \case
    Token.TyOpVar s -> Just s
    _               -> Nothing

uni :: Syntax f => f String
uni = match (const Nothing) (\s -> Uni s)

conid :: Syntax f => f String
conid = match f (\s -> QConId (unqualified s)) where
  f = \case
    QConId n -> if null (qualification n) then Just (unqualify n) else Nothing
    _        -> Nothing

varsym :: Syntax f => f String
varsym = match f (\s -> QVarSym (unqualified s)) where
  f = \case
    QVarSym n -> if null (qualification n) then Just (unqualify n) else Nothing
    _          -> Nothing

lit :: Syntax f => f Lit
lit = match f (\l -> Token.Lit l) where
  f = \case
    Token.Lit l -> Just l
    _           -> Nothing

reservedOp :: Syntax f => String -> f ()
reservedOp s = token (ReservedOp s) <|> mark ("reserved op '" ++ s ++ "'")

reservedCon :: Syntax f => String -> f ()
reservedCon s = token (ReservedCon s) <|> mark ("reserved name '" ++ s ++ "'")

reservedId :: Syntax f => String -> f ()
reservedId s = token (ReservedId s) <|> mark ("reserved name '" ++ s ++ "'")

definePrisms ''Assoc
definePrisms ''Op
definePrisms ''OpRules
definePrisms ''Prec

definePrisms ''DataAlt
definePrisms ''Decl
definePrisms ''Exp
definePrisms ''Pat
definePrisms ''Program
definePrisms ''Stmt
definePrisms ''Tok

definePrisms ''TyOp
definePrisms ''TyPat
definePrisms ''Type
definePrisms ''QType
definePrisms ''QTyVar

definePrisms ''Kind

definePrisms ''KindConstraint
definePrisms ''TypeConstraint

syntax :: (Term a, Syntax f) => I a -> f a
syntax = \case
  -- | Operators
  IAssoc          -> assoc
  IOp             -> op
  IOpRules        -> opRules
  IPrec           -> prec
  -- | T0
  IDataAlt        -> dataAlt
  IDecl           -> decl
  IExp            -> exp
  IPat            -> pat
  IProgram        -> program
  IStmt           -> stmt
  ITok            -> undefined
  -- | T1
  ITyOp           -> tyOp
  ITyPat          -> tyPat
  IType           -> ty
  IQType          -> qTy
  IQTyVar         -> qTyVar
  -- | T2
  IKind           -> kind
  -- | Solver
  ITypeConstraint -> tyConstraint
  IKindConstraint -> kindConstraint


tuple :: (Syntax f, Term a) => Prism a () -> Prism a (Annotated a, Annotated a) -> f a -> f a
tuple unit pair p = special '(' *> tuple' where
  tuple' = unit <$> special ')' *> pure () <|> rightWithSep (special ',') pair p <* special ')'

join :: (Syntax f, Term a) => f a -> (Prism a (Annotated a, b), f b) -> f a
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> unparseable p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

right :: forall f a. (Syntax f, Term a) => Prism a (Annotated a, Annotated a) -> f a -> f a
right = rightWithSep (pure ())

rightWithSep :: forall f a. (Syntax f, Term a) => f () -> Prism a (Annotated a, Annotated a) -> f a -> f a
rightWithSep s _P p = Prism f g <$> annotated p <*> many (s *> annotated p) <|> unparseable p where
  f (p, ps)    = view value (fold p ps)
  fold p = \case
    []     -> p
    (q:qs) -> combine (empty :: f Void) (construct _P) (p, fold q qs)
  g x = case destruct _P x of
    Just (x, y) -> Just (let z:zs = x : unfold y in (z, zs)) -- TODO tidy this up
    Nothing     -> Nothing
  unfold x = case destruct _P (view value x) of
    Just (x, y) -> x : unfold y
    Nothing     -> [x]


tyConstraint :: Syntax f => f TypeConstraint
tyConstraint = _Affine <$> reservedCon "Affine" *> annotated ty <|>
               _Share <$> reservedCon "Share" *> annotated ty <|>
               _Class <$> annotated ty <|>
               _TEq <$> annotated ty <*> reservedOp "~" *> annotated ty <|>
               mark "type constraint"

kindConstraint :: Syntax f => f KindConstraint
kindConstraint = _KEq <$> annotated kind <*> reservedOp "~" *> annotated kind <|>
                mark "kind constraint"

program :: Syntax f => f Program
program = _Program <$> block (annotated top) where -- TODO module
  top = declUsing <|> declData <|> declOp <|> decl -- TODO fixity declarations, imports

declUsing :: Syntax f => f Decl
declUsing = _DeclSyn <$> reservedId "using" *> conid <*> reservedOp "=" *> annotated ty

declData :: Syntax f => f Decl
declData = _DeclData <$> reservedId "type" *> conid <*> many (annotated tyPat) <*> reservedOp "=" *> alts where
  alts = _Singleton <$> annotated dataAlt <|> reservedId "cases" *> block (annotated dataAlt)
  _Singleton = Prism (\x -> [x]) (\case { [x] -> Just x; _ -> Nothing }) -- short definition for a single constructor

dataAlt :: Syntax f => f DataAlt
dataAlt = _DataAlt <$> conid <*> optional (annotated ty)

tyPat :: Syntax f => f TyPat
tyPat = _TyPatVar <$> varid

fun :: Syntax f => f Decl
fun = prefix varid (_DeclSig, sig) (_DeclFun, def) <|> unparseable var <|> mark "function declaration" where
  sig = reservedOp ":" *> annotated qTy
  def = annotated pat `until` reservedOp "=" <*> annotated exp
  var = _DeclVar <$> varid <*> (_Just <$> reservedOp ":" *> annotated qTy) <*> reservedOp "=" *> annotated exp

decl :: Syntax f => f Decl
decl = fun

pat :: Syntax f => f Pat
pat = _PatCon <$> conid <*> optional (annotated pat0) <|> pat0 <|> mark "pattern" where
  pat0 = _PatHole <$> special '_' <|>
         _PatLit <$> lit <|>
         _PatVar <$> varid <|>
         tuple _PatUnit _PatPair pat <|>
         mark "pattern(0)"

kind :: Syntax f => f Kind
kind = kind0 `join` (_KindFun, reservedOp "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindType <$> reservedCon "Type" <|>
          _KindUni <$> uni <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          special '(' *> kind <* special ')' <|>
          mark "kind(0)"

qTy :: Syntax f => f QType
qTy = _Forall <$> (_Cons <$> (reservedId "forall" *> qTyVar) <*> (many qTyVar <* dot) <|> _Nil <$> pure ()) <*> annotated ty <|> mark "quantified type"

qTyVar :: Syntax f => f QTyVar
qTyVar = _QTyVar <$> varid <|>
         _QTyOpVar <$> tyOpVar <|>
          mark "type or type operator variable"

ty :: Syntax f => f Type
ty = ty2 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type" where
  ty2 = _TyOp <$> annotated tyOp <*> annotated ty2 <|> ty1 <|> mark "type(2)"
  ty1 = right _TyApply ty0 <|> mark "type(1)"
  ty0 = _TyVar <$> varid <|>
        _TyCon <$> conid <|>
        _TyUni <$> uni <|>
        tuple _TyUnit _TyPair ty <|>
        mark "type(0)"

tyOp :: Syntax f => f TyOp
tyOp = _TyOpBang <$> reservedOp "&" <|>
       _TyOpUni <$> uni <|>
       _TyOpId <$> reservedOp "<id>" <|>
       _TyOpVar <$> tyOpVar <|>
       mark "type operator"

exp :: Syntax f => f Exp
exp = exp3 `join` (_Sig, reservedOp ":" *> annotated ty) <|> mark "expression" where
  exp3 = mixfix <$> some (annotated (_TOp <$> varsym <|> _TExp <$> annotated exp2)) <|> unparseable exp2 <|> mark "expression(3)" -- FIXME unparseable is a hack here
  mixfix = Prism (\ts -> case ts of { [_ :< TExp e] -> view value e; _ -> Mixfix ts }) (\case { Mixfix ts -> Just ts; _ -> Nothing })
  exp2 = _Read <$> reservedId "read" *> varid <*> reservedId "in" *> annotated exp <|>
         _Do <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         _Lambda <$> reservedOp "\\" *> annotated pat <*> reservedOp "->" *> annotated exp <|>
         exp1 <|> mark "expression(2)"
  exp1 = right _Apply exp0 <|> mark "expression(1)"
  exp0 = _VarBang <$> reservedOp "&" *> varid <|>
         _Var <$> varid <|> -- TODO qualified
         _Con <$> conid <|>
         _Lit <$> lit <|>
         tuple _Unit _Pair exp <|>
         mark "expression(0)"

stmt :: Syntax f => f Stmt
stmt = _StmtDecl <$> reservedId "let" *> annotated decl <|> _StmtExp <$> annotated exp <|> mark "statement"

alt :: Syntax f => f (Annotated Pat, Annotated Exp)
alt = annotated pat <*> reservedOp "->" *> annotated exp <|> mark "case alternative"

declOp :: Syntax f => f Decl
declOp = _DeclOp <$> reservedId "operator" *> annotated op <*> reservedOp "=" *> varid <*> annotated opRules

op :: Syntax f => f Op
op = _Op <$> special '(' *> atLeast 2 atom <* special ')' where
  atom = _Nothing <$> special '_' <|> _Just <$> varsym

opRules :: Syntax f => f OpRules
opRules = _OpMultiRules <$> blockLike (reservedId "where") (_Left <$> annotated assoc <|> _Right <$> precs) <|>
          unparseable (_OpRules <$> reservedId "where" *> special '{' *> optional (annotated assoc <* special ';') <*> precs <* special '}')

-- FIXME contextul reservation is dirty
assoc :: Syntax f => f Assoc
assoc = contextualId "associates" *> assoc' where
  assoc' = _AssocLeft <$> contextualId "left" <|>
           _AssocRight <$> contextualId "right"

precs :: Syntax f => f [Annotated Prec]
precs = blockLike (contextualId "precedence") (annotated prec)

prec :: Syntax f => f Prec
prec = _Prec <$> ordering <*> op where
  ordering = _GT <$> contextualId "above" <|>
             _LT <$> contextualId "below" <|>
             _EQ <$> contextualId "equal"
