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
definePrisms ''TyConstraint
definePrisms ''Prop

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
  ITyConstraint -> tyConstraint
  IKindConstraint -> kindConstraint
  ITyProp       -> unparseable tyProp
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


tyConstraint :: Syntax f => f TyConstraint
tyConstraint = _Share <$> reservedCon "Share" *> annotated ty <|>
               _Class <$> annotated ty <|>
               _TEq <$> annotated ty <*> reservedOp "~" *> annotated ty <|>
               _TOpEq <$> annotated tyOp <*> reservedOp "~" *> annotated tyOp <|>
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
decl = declSyn <|> declData <|> declOp <|> declFun -- TODO imports

declSyn :: Syntax f => f Decl
declSyn = _DeclSyn <$> reservedId "using" *> conid <*> reservedOp "=" *> annotated ty

declData :: Syntax f => f Decl
declData = _DeclData <$> reservedId "type" *> conid <*> optional (annotated tyPat) <*> reservedOp "=" *> alts where
  alts = _Singleton <$> annotated dataAlt <|> reservedId "cases" *> block (annotated dataAlt)
  _Singleton = Prism (\x -> [x]) (\case { [x] -> Just x; _ -> Nothing }) -- short definition for a single constructor

dataAlt :: Syntax f => f DataAlt
dataAlt = _DataAlt <$> conid <*> optional (annotated ty1)

tyPat :: Syntax f => f TyPat
tyPat = _TyPatVar <$> varid <|>
        pack _TyPatPack tyPat

declFun :: Syntax f => f Decl
declFun = prefix varid (_DeclSig, sig) (_DeclFun, def) <|> unparseable var <|> mark "variable/function declaration" where
  sig = reservedOp ":" *> annotated qTy
  def = annotated pat `until` reservedOp "=" <*> annotated exp
  var = _DeclVar <$> varid <*> (_Just <$> reservedOp ":" *> annotated qTy) <*> reservedOp "=" *> annotated exp

-- TODO, merge with declFun? Need to handle parsing ambiguity with @ patterns
bind :: Syntax f => f (Annotated Pat, Annotated Exp)
bind = annotated pat <*> reservedOp "=" *> annotated exp <|> mark "binding"

pat :: Syntax f => f Pat
pat = _PatCon <$> conid <*> optional (annotated pat0) <|> pat0 <|> mark "pattern" where
  pat0 = _PatHole <$> special '_' <|>
         _PatLit <$> litNoString <|> -- TODO allow string literals
         _PatVar <$> varid <|>
         tuple _PatUnit _PatPair pat <|>
         mark "pattern(0)"

kind :: Syntax f => f Kind
kind = kind0 `join` (_KindFun, reservedOp "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindOp <$> reservedCon "Op" <|>
          _KindType <$> reservedCon "Type" <|>
          _KindUni <$> uni <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          tuple1 _KindPair kind <|>
          mark "kind(0)"

qTy :: Syntax f => f QType
qTy = _Forall <$> (_Cons <$> (reservedId "forall" *> qTyVar) <*> (many qTyVar <* dot) <|> _Nil <$> pure ()) <*> annotated ty <|> mark "quantified type"

qTyVar :: Syntax f => f QTyVar
qTyVar = _QTyVar <$> varid <|>
         _QTyOpVar <$> tyOpVar <|>
          mark "type or type operator variable"

ty :: Syntax f => f Type
ty = ty1 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type"

ty1 :: Syntax f => f Type
ty1 = right _TyApply ty0 <|> mark "type(1)" where
  ty0 = _TyOp  <$> annotated tyOp <|>
        _TyVar <$> varid <|>
        _TyCon <$> conid <|>
        _TyUni <$> uni <|>
        pack _TyPack ty <|>
        tuple _TyUnit _TyPair ty <|>
        mark "type(0)"

tyOp :: Syntax f => f TyOp
tyOp = _TyOpBang <$> reservedOp "&" <|>
       _TyOpUni <$> uni <|>
       _TyOpId <$> contextualId "id" <|>
       _TyOpVar <$> tyOpVar <|>
       mark "type operator"

exp :: Syntax f => f Exp
exp = exp4 `join` (_Sig, reservedOp ":" *> annotated ty) <|> mark "expression" where
  -- TODO should mixfix be at this high a level?
  exp4 = mixfix <$> some (annotated (_TOp <$> varsym <|> _TExp <$> annotated exp3)) <|> unparseable exp3 <|> mark "expression(4)" -- FIXME unparseable is a hack here
  mixfix = Prism (\ts -> case ts of { [_ :< TExp e] -> view value e; _ -> Mixfix ts }) (\case { Mixfix ts -> Just ts; _ -> Nothing })
  exp3 = optWhere <$> annotated exp2 <*> blockLike (reservedId "where") (annotated declFun) <|> unparseable exp2 <|> mark "expression(3)"
  optWhere = Prism (\(e, ps) -> case ps of { [] -> view value e; _ -> Where e ps }) (\case { Where e ps -> Just (e, ps); _ -> Nothing })
  exp2 = _Read <$> reservedId "read" *> varid <*> reservedId "in" *> annotated exp <|>
         _Do <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         _If <$> reservedId "if" *> annotated exp <*> reservedId "then" *> annotated exp <*> reservedId "else" *> annotated exp <|>
         _Lambda <$> reservedOp "\\" *> alt <|>
         _Let <$> reservedId "let" *> bind <*> reservedId "in" *> annotated exp <|>
         _Switch <$> reservedId "switch" *> block switch <|>
         exp1 <|> mark "expression(2)"
  exp1 = right _Apply exp0 <|> mark "expression(1)"
  exp0 = _VarBang <$> reservedOp "&" *> varid <|>
         _Var <$> varid <|> -- TODO qualified
         _Con <$> conid <|>
         _Lit <$> lit <|>
         tuple _Unit _Pair exp <|>
         mark "expression(0)"

switch :: Syntax f => f (Annotated Exp, Annotated Exp)
switch = annotated exp <*> reservedOp "->" *> annotated exp <|> mark "switch alternative"

-- TODO allow "let ... in" in expression?
stmt :: Syntax f => f Stmt
stmt = _StmtDecl <$> reservedId "let" *> annotated declFun <|> _StmtExp <$> annotated exp <|> mark "statement"

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
