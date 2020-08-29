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
import           Record        (Record)
import qualified Record
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

-- FIXME contextule reservation is dirty
contextualOp :: Syntax f => Name -> f ()
contextualOp op = token (QVarSym (unqualified op)) <|> mark ("contextually-reserved '" ++ op ++ "'")

contextualId :: Syntax f => Name -> f ()
contextualId id = token (QVarId (unqualified id)) <|> mark ("contextually-reserved '" ++ id ++ "'")

dot :: Syntax f => f ()
dot = contextualOp "."

block :: Syntax f => f a -> f [a]
block p = special '{' *> _Cons <$> p <*> (special ';' *> p) `until` special '}'

blockOrLine :: Syntax f => f a -> f (a, [a])
blockOrLine f = special '{' *> f <*> (special ';' *> f) `until` special '}' <|>
                f <*> _Nil <$> pure ()

blockLike :: Syntax f => f () -> f a -> f [a]
blockLike f g = _Cons <$> f *> blockOrLine g <|>
                _Nil <$> pure ()

list :: Syntax f => f a -> f [a]
list p = special '(' *> (_Nil <$> special ')' *> pure () <|> _Cons <$> p <*> (special ',' *> p) `until` special ')')

-- This also captures parenthesised p's (which is corrected by desugaring)
record :: Syntax f => f a -> f (Record a)
record p = f <$> list p' where
  p' = Prism (\v -> (Nothing, v)) (Just . snd) <$> p -- TODO named fields
  f = Prism (\r -> Record.fromList r) (\kvs -> Just (map (\(_, v) -> (Nothing, v)) (Record.toList kvs)))

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
  top = declData <|> declOp <|> decl -- TODO fixity declarations, imports

declData :: Syntax f => f Decl
declData = _DeclData <$> reservedId "data" *> conid <*> many (annotated tyPat) <*> alts where
  alts = blockLike (reservedId "where") (annotated dataAlt)

dataAlt :: Syntax f => f DataAlt
dataAlt = _DataAlt <$> conid <*> many (annotated ty)

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
pat = _PatCon <$> conid <*> many (annotated pat0) <|> pat0 <|> mark "pattern" where
  pat0 = _PatHole <$> special '_' <|>
         _PatRecord <$> record (annotated pat) <|>
         _PatLit <$> lit <|>
         _PatVar <$> varid <|>
         special '(' *> pat <* special ')' <|>
         mark "pattern(0)"

join :: (Syntax f, Term a) => f a -> (Prism a (Annotated a, b), f b) -> f a
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> unparseable p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

left :: forall f a. (Syntax f, Term a) => Prism a (Annotated a, Annotated a) -> f a -> f a
left _P p = Prism f g <$> annotated p <*> many (annotated p) <|> unparseable p where
  f (_ :< p, []) = p
  f (p, q:qs)    = fold p q qs
  fold p q []     = construct _P (p, q)
  fold p q (r:rs) = fold (combine (empty :: f Void) (construct _P) (p, q)) r rs
  g x = case destruct _P x of
    Just (x, y) -> Just (let z:zs = unfold x ++ [y] in (z, zs)) -- TODO tidy this up
    Nothing     -> Nothing
  unfold x = case destruct _P (view value x) of
    Just (x, y) -> unfold x ++ [y]
    Nothing     -> [x]

kind :: Syntax f => f Kind
kind = kind0 `join` (_KindFun, reservedOp "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindType <$> reservedCon "Type" <|>
          _KindUni <$> uni <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          special '(' *> kind <* special ')' <|>
          mark "kind(0)"

qTy :: Syntax f => f QType
qTy = _Forall <$> reservedId "forall" *> qTyVar `until` dot <*> annotated ty <|>
      _Mono <$> annotated ty <|>
      mark "quantified type"

qTyVar :: Syntax f => f QTyVar
qTyVar = _QTyVar <$> varid <|>
         _QTyOpVar <$> tyOpVar <|>
          mark "type or type operator variable"

ty :: Syntax f => f Type
ty = ty2 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type" where
  ty2 = _TyOp <$> annotated tyOp <*> annotated ty2 <|> ty1 <|> mark "type(2)"
  ty1 = left _TyApply ty0 <|> mark "type(1)"
  ty0 = _TyVar <$> varid <|>
        _TyCon <$> conid <|>
        _TyRecord <$> record (annotated ty) <|>
        _TyUni <$> uni <|>
        special '(' *> ty <* special ')' <|>
        mark "type(0)"

tyOp :: Syntax f => f TyOp
tyOp = _TyOpBang <$> reservedOp "!" <|>
       _TyOpUni <$> uni <|>
       _TyOpId <$> reservedOp "<id>" <|>
       _TyOpVar <$> tyOpVar <|>
       mark "type operator"

exp :: Syntax f => f Exp
exp = exp3 `join` (_Sig, reservedOp ":" *> annotated ty) <|> mark "expression" where
  exp3 = _Mixfix <$> some (annotated (_TOp <$> varsym <|> _TExp <$> annotated exp2)) <|> unparseable exp2 <|> mark "expression(3)" -- FIXME unparseable is a hack here
  exp2 = _Read <$> reservedId "read" *> varid <*> reservedId "in" *> annotated exp <|>
         _Do <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         _Lambda <$> reservedOp "\\" *> annotated pat <*> reservedOp "->" *> annotated exp <|>
         exp1 <|> mark "expression(2)"
  exp1 = left _Apply exp0 <|> mark "expression(1)"
  exp0 = _Record <$> record (annotated exp) <|>
         _VarBang <$> reservedOp "!" *> varid <|>
         _Var <$> varid <|> -- TODO qualified
         _Con <$> conid <|>
         _Lit <$> lit <|>
         special '(' *> exp <* special ')' <|>
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
