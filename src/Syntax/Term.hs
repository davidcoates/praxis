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
uni = match (const Nothing) (\s -> Uni s) where

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

syntax :: (Recursive a, Syntax f, Domain f s) => I a -> f (a s)
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

tyConstraint :: (Syntax f, Domain f s) => f (TypeConstraint s)
tyConstraint = _Class <$> annotated ty <|>
               _TEq <$> annotated ty <*> reservedOp "~" *> annotated ty <|>
               mark "type constraint"

kindConstraint :: (Syntax f, Domain f s) => f (KindConstraint s)
kindConstraint = _KEq <$> annotated kind <*> reservedOp "~" *> annotated kind <|>
                mark "kind constraint"

program :: (Syntax f, Domain f s) => f (Program s)
program = _Program <$> block (annotated top) where -- TODO module
  top = declData <|> decl -- TODO fixity declarations, imports

declData :: (Syntax f, Domain f s) => f (Decl s)
declData = _DeclData <$> reservedId "data" *> conid <*> many (annotated tyPat) <*> alts where
  alts = cons <$> reservedId "where" *> lbrace *> annotated dataAlt <*> (semi *> annotated dataAlt) `until` rbrace <|> -- TODO clean this up
         nil <$> pure ()

dataAlt :: (Syntax f, Domain f s) => f (DataAlt s)
dataAlt = _DataAlt <$> conid <*> many (annotated ty)

tyPat :: (Syntax f, Domain f s) => f (TyPat s)
tyPat = _TyPatVar <$> varid

fun :: (Syntax f, Domain f s) => f (Decl s)
fun = prefix varid (_DeclSig, sig) (_DeclFun, def) <|> unparseable var <|> mark "function declaration" where
  sig = reservedOp ":" *> annotated qty
  def = annotated pat `until` reservedOp "=" <*> annotated exp
  var = _DeclVar <$> varid <*> (maybe <$> reservedOp ":" *> annotated qty) <*> reservedOp "=" *> annotated exp

decl :: (Syntax f, Domain f s) => f (Decl s)
decl = fun

pat :: (Syntax f, Domain f s) => f (Pat s)
pat = _PatCon <$> conid <*> many (annotated pat0) <|> pat0 <|> mark "pattern" where
  pat0 = _PatHole <$> special '_' <|>
         _PatRecord <$> record (annotated pat) <|>
         _PatLit <$> lit <|>
         _PatVar <$> varid <|>
         special '(' *> pat <* special ')' <|>
         mark "pattern(0)"

join :: (Syntax f, Domain f s, Recursive a) => f (a s) -> (Prism (a s) (Annotated s a, b), f b) -> f (a s)
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> unparseable p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

left :: forall f a s. (Syntax f, Domain f s, Recursive a) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
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

kind :: (Syntax f, Domain f s) => f (Kind s)
kind = kind0 `join` (_KindFun, reservedOp "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindType <$> reservedCon "Type" <|>
          _KindUni <$> uni <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          special '(' *> kind <* special ')' <|>
          mark "kind(0)"

qty :: (Syntax f, Domain f s) => f (QType s)
qty = _Forall <$> reservedId "forall" *> varid `until` dot <*> annotated ty <|>
      _Mono <$> annotated ty

ty :: (Syntax f, Domain f s) => f (Type s)
ty = ty2 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type" where
  ty2 = _TyOp <$> annotated tyOp <*> annotated ty <|> ty1 <|> mark "type(2)"
  ty1 = left _TyApply ty0 <|> mark "type(1)"
  ty0 = _TyVar <$> varid <|>
        _TyCon <$> conid <|>
        _TyRecord <$> record (annotated ty) <|>
        _TyUni <$> uni <|>
        special '(' *> ty <* special ')' <|>
        mark "type(0)"

tyOp :: (Syntax f, Domain f s) => f (TyOp s)
tyOp = _TyOpBang <$> reservedOp "!" <|>
       unparseable (_TyOpUni <$> uni) <|>
       unparseable (_TyOpId <$> token (Print "id")) <|> -- keep track of where we have (TyOp TyOpId t) instead of (t)
       mark "tyOp" -- TODO TyOpVar

exp :: (Syntax f, Domain f s) => f (Exp s)
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

stmt :: (Syntax f, Domain f s) => f (Stmt s)
stmt = _StmtDecl <$> reservedId "let" *> annotated decl <|> _StmtExp <$> annotated exp <|> mark "statement"

alt :: (Syntax f, Domain f s) => f (Annotated s Pat, Annotated s Exp)
alt = annotated pat <*> reservedOp "->" *> annotated exp <|> mark "case alternative"
