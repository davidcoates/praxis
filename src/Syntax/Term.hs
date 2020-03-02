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

import           Prelude       hiding (exp, maybe, pure, until, (*>), (<$>),
                                (<*), (<*>))

-- TODO move this elsewhere?
definePrisms ''Either
prefix :: Syntax f => f a -> (Prism d (a, b), f b) -> (Prism d (a, c), f c) -> f d
prefix a (l, b) (r, c) = Prism f g <$> a <*> (_Left <$> b <|> _Right <$> c) where
  f (a, Left x)  = construct l (a, x)
  f (a, Right x) = construct r (a, x)
  g d = case (destruct l d, destruct r d) of
    (Just (a, x), Nothing) -> Just (a, Left x)
    (Nothing, Just (a, x)) -> Just (a, Right x)
    (Nothing, Nothing)     -> Nothing

until :: Syntax f => f a -> f () -> f [a]
until p q = nil <$> q <|> cons <$> p <*> until p q

token :: Syntax f => Token -> f ()
token t = match (\t' -> if t' == t then Just () else Nothing) (const t)

special :: Syntax f => Char -> f ()
special c = token (Special c) <|> mark ("special '" ++ [c] ++ "'")

dot :: Syntax f => f ()
dot = token (QVarSym (QString [] ".")) <|> mark "contextually-reserved '.'"

lbrace :: Syntax f => f ()
lbrace = special '{'

rbrace :: Syntax f => f ()
rbrace = special '}'

semi :: Syntax f => f ()
semi = special ';'

comma :: Syntax f => f ()
comma = special ','

block :: Syntax f => f a -> f [a]
block p = lbrace *> cons <$> p <*> (semi *> p) `until` rbrace

list :: Syntax f => f a -> f [a]
list p = special '(' *> (nil <$> special ')' *> pure () <|> cons <$> p <*> (comma *> p) `until` special ')')

-- This also captures parenthesised p's (which is corrected by desugaring)
record :: Syntax f => f a -> f (Record a)
record p = f <$> list p' where
  p' = Prism (\v -> (Nothing, v)) (Just . snd) <$> p -- TODO named fields
  f = Prism (\r -> Record.fromList r) (\kvs -> Just (map (\(_, v) -> (Nothing, v)) (Record.toList kvs)))

varid :: Syntax f => f String
varid = match f (\s -> QVarId (QString [] s)) where
  f = \case
    QVarId n -> if null (qualification n) then Just (name n) else Nothing
    _        -> Nothing

uni :: Syntax f => f String
uni = unparseable $ match (const Nothing) (\s -> Uni s)

conid :: Syntax f => f String
conid = match f (\s -> QConId (QString [] s)) where
  f = \case
    QConId n -> if null (qualification n) then Just (name n) else Nothing
    _        -> Nothing

qvarsym :: Syntax f => f QString
qvarsym = match f QVarSym where
  f = \case
    QVarSym n -> Just n
    _         -> Nothing

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

definePrisms ''Kind

definePrisms ''KindConstraint
definePrisms ''TypeConstraint

syntax :: (Recursive a, Syntax f) => I a -> f a
syntax = \case
  IDataAlt        -> dataAlt
  IDecl           -> decl
  IExp            -> exp
  IKind           -> kind
  IPat            -> pat
  IProgram        -> program
  IQType          -> qty
  IStmt           -> stmt
  ITok            -> undefined
  ITyOp           -> tyOp
  ITyPat          -> tyPat
  IType           -> ty
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
  top = declData <|> decl -- TODO fixity declarations, imports

declData :: Syntax f => f Decl
declData = _DeclData <$> reservedId "data" *> conid <*> many (annotated tyPat) <*> alts where
  alts = cons <$> reservedId "where" *> lbrace *> annotated dataAlt <*> (semi *> annotated dataAlt) `until` rbrace <|> -- TODO clean this up
         nil <$> pure ()

dataAlt :: Syntax f => f DataAlt
dataAlt = _DataAlt <$> conid <*> many (annotated ty)

tyPat :: Syntax f => f TyPat
tyPat = _TyPatVar <$> varid

fun :: Syntax f => f Decl
fun = prefix varid (_DeclSig, sig) (_DeclFun, def) <|> unparseable var <|> mark "function declaration" where
  sig = reservedOp ":" *> annotated qty
  def = annotated pat `until` reservedOp "=" <*> annotated exp
  var = _DeclVar <$> varid <*> (maybe <$> reservedOp ":" *> annotated qty) <*> reservedOp "=" *> annotated exp

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

join :: (Syntax f, Recursive a) => f a -> (Prism a (Annotated a, b), f b) -> f a
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> unparseable p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

left :: forall f a. (Syntax f, Recursive a) => Prism a (Annotated a, Annotated a) -> f a -> f a
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

qty :: Syntax f => f QType
qty = _Forall <$> reservedId "forall" *> varid `until` dot <*> annotated ty <|>
      _Mono <$> annotated ty

ty :: Syntax f => f Type
ty = ty2 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type" where
  ty2 = _TyOp <$> annotated tyOp <*> annotated ty <|> ty1 <|> mark "type(2)"
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
       mark "type operator" -- TODO TyOpVar

exp :: Syntax f => f Exp
exp = exp3 `join` (_Sig, reservedOp ":" *> annotated ty) <|> mark "expression" where
  exp3 = _Mixfix <$> some (annotated (_TOp <$> qvarsym <|> _TExp <$> annotated exp2)) <|> unparseable exp2 <|> mark "expression(3)" -- FIXME unparseable is a hack here
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
