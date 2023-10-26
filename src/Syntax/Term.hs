{-# LANGUAGE ConstraintKinds       #-}
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

contextualOp :: Syntax f => Name -> f ()
contextualOp op = token (QVarSym (unqualified op)) <|> unparseable (reservedOp op) <|> mark ("contextually keyword '" ++ op ++ "'")

contextualId :: Syntax f => Name -> f ()
contextualId id = token (QVarId (unqualified id)) <|> unparseable (reservedId id) <|> mark ("contextual keyword '" ++ id ++ "'")

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
    _         -> Nothing

lit :: Syntax f => f Lit
lit = match f (\l -> Token.Lit l) where
  f = \case
    Token.Lit l -> Just l
    _           -> Nothing

litNoString :: Syntax f => f Lit
litNoString = match f (\l -> Token.Lit l) where
  f = \case
    Token.Lit (String _) -> Nothing
    Token.Lit l          -> Just l
    _                    -> Nothing

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

definePrisms ''Bind
definePrisms ''DataCon
definePrisms ''Decl
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
definePrisms ''Prop

-- | The syntax for a given term type.
syntax :: (Term a, Syntax f) => I a -> f a
syntax = \case
  -- | Operators
  IAssoc          -> assoc
  IOp             -> op
  IOpRules        -> opRules
  IPrec           -> prec
  -- | T0
  IDataCon        -> dataAlt
  IDecl           -> decl
  IExp            -> exp
  IPat            -> pat
  IProgram        -> program
  IStmt           -> stmt
  ITok            -> undefined
  -- | T1
  IView           -> view'
  ITyPat          -> tyPat
  IType           -> ty
  IQType          -> qTy
  IQTyVar         -> qTyVar
  -- | T2
  IKind           -> kind
  -- | Solver
  ITyConstraint   -> tyConstraint
  IKindConstraint -> kindConstraint
  ITyProp         -> unparseable tyProp
  IKindProp       -> unparseable kindProp


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

right :: forall f a. (Syntax f, Term a) => Prism a (Annotated a, Annotated a) -> f a -> f a
right = rightWithSep (pure ())

rightWithSep :: forall f a. (Syntax f, Term a) => f () -> Prism a (Annotated a, Annotated a) -> f a -> f a
rightWithSep s _P p = Prism f g <$> annotated p <*> (s *> (_Just <$> annotated (rightWithSep s _P p)) <|> _Nothing <$> pure ()) <|> unparseable p where
  f (p, Just q)  = construct _P (p, q)
  f (p, Nothing) = view value p
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

tyConstraint :: Syntax f => f TyConstraint
tyConstraint = _Share <$> reservedCon "Share" *> annotated ty <|>
               _Class <$> annotated ty <|>
               unparseable (_RefFree <$> varid <*> reservedId "ref-free" *> annotated ty) <|>
               _TEq <$> annotated ty <*> reservedOp "~" *> annotated ty <|>
               unparseable (_TOpEq <$> annotated ty <*> reservedOp "o~" *> annotated ty) <|>
               mark "type constraint"

kindConstraint :: Syntax f => f KindConstraint
kindConstraint = _KEq <$> annotated kind <*> reservedOp "~" *> annotated kind <|>
                mark "kind constraint"

tyProp :: Syntax f => f TyProp
tyProp = _Exactly <$> tyConstraint <|>
         _Top <$> special '⊤' <|>
         _Bottom <$> special '⊥' <|>
         _And <$> tyProp <*> special '∧' *> tyProp

kindProp :: Syntax f => f KindProp
kindProp = _Exactly <$> kindConstraint <|>
           _Top <$> special '⊤' <|>
           _Bottom <$> special '⊥' <|>
           _And <$> kindProp <*> special '∧' *> kindProp

program :: Syntax f => f Program
program = _Program <$> block (annotated decl) where -- TODO module

decl :: Syntax f => f Decl
decl = declSyn <|> declData <|> declOp <|> declTerm -- TODO imports

declSyn :: Syntax f => f Decl
declSyn = _DeclSyn <$> reservedId "using" *> conid <*> reservedOp "=" *> annotated ty

declData :: Syntax f => f Decl
declData = _DeclData <$> reservedId "type" *> conid <*> optional (annotated tyPat) <*> reservedOp "=" *> alts where
  alts = _Singleton <$> annotated dataAlt <|> reservedId "cases" *> block (annotated dataAlt)
  _Singleton = Prism (\x -> [x]) (\case { [x] -> Just x; _ -> Nothing }) -- short definition for a single constructor

dataAlt :: Syntax f => f DataCon
dataAlt = _DataCon <$> conid <*> optional (annotated ty1)

tyPat :: Syntax f => f TyPat
tyPat = tyPat0 <|> pack _TyPatPack tyPat0 <|> mark "type pattern" where
  tyPat0 = _TyPatVar <$> varid <|>
           _TyPatViewVar <$> viewDomain <*> varid <|>
           unparseable (pack _TyPatPack tyPat) <|>
           mark "type pattern(0)"

declTerm :: Syntax f => f Decl
declTerm = prefix varid (_DeclSig, declSig) (_DeclDef, declDef) <|> declRec <|> unparseable declVar <|> mark "term declaration/definition" where
  declRec = _DeclRec <$> blockLike (reservedId "rec") (annotated declTerm)
  declSig = reservedOp ":" *> annotated qTy
  declDef = annotated pat `until` reservedOp "=" <*> annotated exp
  declVar = _DeclTerm <$> varid <*> (_Just <$> reservedOp ":" *> annotated qTy) <*> reservedOp "=" *> annotated exp

bind :: Syntax f => f Bind
bind = _Bind <$> annotated pat <*> reservedOp "=" *> annotated exp <|> mark "binding"

pat :: Syntax f => f Pat
pat = _PatCon <$> conid <*> optional (annotated pat0) <|> pat0 <|> mark "pattern" where
  pat0 = _PatHole <$> special '_' <|>
         _PatLit <$> litNoString <|> -- TODO allow string literals
         _PatVar <$> varid <|>
         tuple _PatUnit _PatPair pat <|>
         mark "pattern(0)"

kind :: Syntax f => f Kind
kind = kind0 `join` (_KindFun, reservedOp "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindView <$> reservedCon "View" <|>
          _KindType <$> reservedCon "Type" <|>
          unparseable (_KindUni <$> uni) <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          tuple1 _KindPair kind <|>
          mark "kind(0)"

qTy :: Syntax f => f QType
qTy = _Forall <$> (_Cons <$> (reservedId "forall" *> annotated qTyVar) <*> (many (annotated qTyVar) <* dot) <|> _Nil <$> pure ()) <*> tyConstraints <*> annotated ty <|> mark "quantified type"

tyConstraints :: Syntax f => f [Annotated TyConstraint]
tyConstraints = _Cons <$> (contextualOp "[" *> annotated tyConstraint) <*> tyConstraints' <|> _Nil <$> pure () where
  tyConstraints' :: Syntax f => f [Annotated TyConstraint]
  tyConstraints' = _Cons <$> (annotated tyConstraint <* special ',') <*>  tyConstraints' <|>
                   _Nil <$> (contextualOp "]" *> reservedOp "=>")

qTyVar :: Syntax f => f QTyVar
qTyVar = _QTyVar <$> varid <|>
         _QViewVar <$> viewDomain <*> varid <|>
          mark "type variable"

ty :: Syntax f => f Type
ty = ty1 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type"

viewDomain :: Syntax f => f ViewDomain
viewDomain = _Ref <$> reservedOp "&" <|>
             _RefOrValue <$> reservedOp "?" <|>
             mark "view domain"

ty1 :: Syntax f => f Type
ty1 = right _TyApply ty0 <|> mark "type(1)" where
  ty0 = _View  <$> annotated view' <|>
        _TyVar <$> varid <|>
        _TyCon <$> conid <|>
        unparseable (_TyUni <$> uni) <|>
        pack _TyPack ty <|>
        tuple _TyUnit _TyPair ty <|>
        mark "type(0)"

view' :: Syntax f => f View
view' = unparseable (_ViewUni <$> viewDomain <*> uni) <|>
        unparseable (_ViewRef <$> reservedOp "&" *> varid) <|>
        unparseable (_ViewValue <$> contextualId "«value-view»") <|>
        _ViewVar <$> viewDomain <*> varid <|>
        mark "view"

exp :: Syntax f => f Exp
exp = exp4 `join` (_Sig, reservedOp ":" *> annotated ty) <|> mark "expression" where
  -- TODO should mixfix be at this high a level?
  exp4 = mixfix <$> some (annotated (_TOp <$> varsym <|> _TExp <$> annotated exp3)) <|> unparseable exp3 <|> mark "expression(4)" -- FIXME unparseable is a hack here
  mixfix = Prism (\ts -> case ts of { [_ :< TExp e] -> view value e; _ -> Mixfix ts }) (\case { Mixfix ts -> Just ts; _ -> Nothing })
  exp3 = optWhere <$> annotated exp2 <*> blockLike (reservedId "where") (annotated declTerm) <|> unparseable exp2 <|> mark "expression(3)"
  optWhere = Prism (\(e, ps) -> case ps of { [] -> view value e; _ -> Where e ps }) (\case { Where e ps -> Just (e, ps); _ -> Nothing })
  exp2 = _Read <$> reservedId "read" *> varid <*> reservedId "in" *> annotated exp <|>
         _Do <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         _If <$> reservedId "if" *> annotated exp <*> reservedId "then" *> annotated exp <*> reservedId "else" *> annotated exp <|>
         _Lambda <$> reservedOp "\\" *> alt <|>
         _Let <$> reservedId "let" *> annotated bind <*> reservedId "in" *> annotated exp <|>
         _Switch <$> reservedId "switch" *> block switch <|>
         exp1 <|> mark "expression(2)"
  exp1 = right _Apply exp0 <|> mark "expression(1)"
  exp0 = _VarRef <$> reservedOp "&" *> varid <|>
         _Var <$> varid <|> -- TODO qualified
         _Con <$> conid <|>
         _Lit <$> lit <|>
         tuple _Unit _Pair exp <|>
         mark "expression(0)"

switch :: Syntax f => f (Annotated Exp, Annotated Exp)
switch = annotated exp <*> reservedOp "->" *> annotated exp <|> mark "switch alternative"

-- TODO allow "let ... in" in expression?
stmt :: Syntax f => f Stmt
stmt = _StmtBind <$> reservedId "let" *> annotated bind <|> _StmtExp <$> annotated exp <|> mark "statement"

alt :: Syntax f => f (Annotated Pat, Annotated Exp)
alt = annotated pat <*> reservedOp "->" *> annotated exp <|> mark "case alternative"

declOp :: Syntax f => f Decl
declOp = _DeclOp <$> reservedId "operator" *> annotated op <*> reservedOp "=" *> varid <*> annotated opRules

op :: Syntax f => f Op
op = _Op <$> special '(' *> atLeast 2 atom <* special ')' where
  atom = _Nothing <$> special '_' <|> _Just <$> varsym

opRules :: Syntax f => f OpRules
opRules = _OpMultiRules <$> blockLike (reservedId "where") (_Left <$> annotated assoc <|> _Right <$> precs) <|>
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
