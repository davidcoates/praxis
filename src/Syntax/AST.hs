{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Syntax.AST
  ( syntax
  ) where

import           AST
import           Common
import           Introspect
import           Kind
import           Record        (Record)
import qualified Record
import qualified Syntax.Kind   as Kind
import           Syntax.Prism
import           Syntax.Syntax
import           Syntax.TH
import qualified Syntax.Type   as Type
import           Token
import           Type

import           Prelude       hiding (exp, log, maybe, pure, until, (*>),
                                (<$>), (<*), (<*>))

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

list :: Syntax f => Char -> f a -> Char -> f [a]
list l p r = special l *> (nil <$> special r *> pure () <|> cons <$> p <*> (comma *> p) `until` special r)

-- This also captures parenthesised p's (which is corrected by desugaring)
record :: Syntax f => Char -> f a -> Char -> f (Record a)
record l p r = f <$> list l p' r where
  p' = Prism (\v -> (Nothing, v)) (Just . snd) <$> p -- TODO named fields
  f = Prism (\r -> Record.fromList r) (\kvs -> Just (map (\(_, v) -> (Nothing, v)) (Record.toList kvs)))

varid :: Syntax f => f String
varid = match f (\s -> QVarId (QString [] s)) where
  f t = case t of
    QVarId n -> if null (qualification n) then Just (name n) else Nothing
    _        -> Nothing

uni :: Syntax f => f String
uni = match (const Nothing) (\s -> Uni s) where

conid :: Syntax f => f String
conid = match f (\s -> QConId (QString [] s)) where
  f t = case t of
    QConId n -> if null (qualification n) then Just (name n) else Nothing
    _        -> Nothing

qvarsym :: Syntax f => f QString
qvarsym = match f QVarSym where
  f t = case t of
    QVarSym n -> Just n
    _         -> Nothing

lit :: Syntax f => f Lit
lit = match f (\l -> Token.Lit l) where
  f t = case t of
    Token.Lit l -> Just l
    _           -> Nothing

reservedOp :: Syntax f => String -> f ()
reservedOp s = token (ReservedOp s) <|> mark ("reserved op '" ++ s ++ "'")

reservedCon :: Syntax f => String -> f ()
reservedCon s = token (ReservedCon s) <|> mark ("reserved name '" ++ s ++ "'")

reservedId :: Syntax f => String -> f ()
reservedId s = token (ReservedId s) <|> mark ("reserved name '" ++ s ++ "'")

definePrisms ''Decl
definePrisms ''Program
definePrisms ''Exp
definePrisms ''Pat
definePrisms ''Type
definePrisms ''QType
definePrisms ''Kind
definePrisms ''Tok
definePrisms ''Stmt

syntax :: (Recursive a, Syntax f, Domain f s) => I a -> f (a s)
syntax x = case x of
  IDataAlt        -> undefined
  IDecl           -> decl
  IExp            -> exp
  IKind           -> kind
  IPat            -> pat
  IProgram        -> program
  IQType          -> undefined
  IStmt           -> stmt
  ITok            -> undefined
  ITyPat          -> undefined
  IType           -> ty
  ITypeConstraint -> tyConstraint
  IKindConstraint -> kindConstraint

tyConstraint :: (Syntax f, Domain f s) => f (Type.Constraint s)
tyConstraint = Type._Class <$> annotated ty <|>
               Type._Eq <$> annotated ty <*> reservedOp "~" *> annotated ty <|>
               mark "type constraint"

kindConstraint :: (Syntax f, Domain f s) => f (Kind.Constraint s)
kindConstraint = undefined

program :: (Syntax f, Domain f s) => f (Program s)
program = _Program <$> block (annotated top) where -- TODO module
  top = fun -- TODO fixity declarations, imports

fun :: (Syntax f, Domain f s) => f (Decl s)
fun = prefix varid (_DeclSig, sig) (_DeclFun, def) <|> unparseable var <|> mark "function declaration" where
  sig = reservedOp ":" *> annotated qty
  def = annotated pat `until` reservedOp "=" <*> annotated exp
  var = _DeclVar <$> varid <*> (maybe <$> reservedOp ":" *> annotated qty) <*> reservedOp "=" *> annotated exp

decl :: (Syntax f, Domain f s) => f (Decl s)
decl = fun

pat :: (Syntax f, Domain f s) => f (Pat s)
pat = _PatHole <$> special '_' <|>
      _PatRecord <$> record '(' (annotated pat) ')' <|>
      _PatLit <$> lit <|>
      _PatVar <$> varid <|>
      mark "pattern"

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
          _KindConstraint <$> reservedCon "Constraint" <|>
          _KindRecord <$> record '[' (annotated kind) ']' <|>
          special '(' *> kind <* special ')' <|>
          mark "kind(0)"

qty :: (Syntax f, Domain f s) => f (QType s)
qty = _Forall <$> reservedId "forall" *> varid `until` dot <*> annotated ty <|>
      _Mono <$> annotated ty

ty :: (Syntax f, Domain f s) => f (Type s)
ty = ty1 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type" where
  ty1 = left _TyApply ty0 <|> mark "type(1)"
  ty0 = _TyVar <$> varid <|>
        _TyCon <$> conid <|>
        _TyRecord <$> record '(' (annotated ty) ')' <|>
        _TyPack <$> record '[' (annotated ty) ']' <|>
        _TyUni <$> uni <|>
        special '(' *> ty <* special ')' <|>
        mark "type(0)"

exp :: (Syntax f, Domain f s) => f (Exp s)
exp = exp3 `join` (_Sig, reservedOp ":" *> annotated ty) <|> mark "exp" where
  exp3 = _Mixfix <$> some (annotated (_TOp <$> qvarsym <|> _TExp <$> annotated exp2)) <|> unparseable exp2 <|> mark "exp(3)" -- FIXME unparseable is a hack here
  exp2 = _Read <$> reservedId "read" *> varid <*> reservedId "in" *> annotated exp <|>
         _Do <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         _Lambda <$> reservedOp "\\" *> annotated pat <*> reservedOp "->" *> annotated exp <|>
         exp1 <|> mark "exp(2)"
  exp1 = left _Apply exp0 <|> mark "exp(1)"
  exp0 = _Record <$> record '(' (annotated exp) ')' <|>
         _Var <$> varid <|>
         _Lit <$> lit <|>
         special '(' *> exp <* special ')' <|>
         mark "exp(0)"

stmt :: (Syntax f, Domain f s) => f (Stmt s)
stmt = _StmtDecl <$> reservedId "let" *> annotated decl <|> _StmtExp <$> annotated exp <|> mark "stmt"

alt :: (Syntax f, Domain f s) => f (Annotated s Pat, Annotated s Exp)
alt = annotated pat <*> reservedOp "->" *> annotated exp <|> mark "alt"
