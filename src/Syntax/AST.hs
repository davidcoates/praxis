{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Syntax.AST
  ( Syntactic(..)
  ) where

import           AST
import           Common
import           Introspect    (Recursive)
import           Kind
import           Record        (Record)
import qualified Record
import           Syntax.Prism
import           Syntax.Syntax
import           Syntax.TH
import           Token
import           Type

import           Prelude       hiding (exp, log, pure, until, (*>), (<$>), (<*),
                                (<*>))

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
list l p r = special l *> (special r *> nil <$> pure () <|> cons <$> p <*> (comma *> p) `until` special r)

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
definePrisms ''Kind
definePrisms ''Tok
definePrisms ''Stmt

class Recursive a => Syntactic a where
  syntax :: (Syntax f, Domain f s) => f (a s)

instance Syntactic Program where
  syntax = program

instance Syntactic Exp where
  syntax = exp

instance Syntactic Type where
  syntax = ty

instance Syntactic Kind where
  syntax = kind

program :: (Syntax f, Domain f s) => f (Program s)
program = _Program <$> block (annotated top) where -- TODO module
  top = fun -- TODO fixity declarations, imports

fun :: (Syntax f, Domain f s) => f (Decl s)
fun = prefix varid (_DeclSig, sig) (_DeclFun, def) where
  sig = reservedOp ":" *> annotated ty -- TODO qty
  def = annotated pat `until` reservedOp "=" <*> annotated exp

decl :: (Syntax f, Domain f s) => f (Decl s)
decl = fun

pat :: (Syntax f, Domain f s) => f (Pat s)
pat = _PatHole <$> special '_' <|>
      _PatRecord <$> record '(' (annotated pat) ')' <|>
      _PatLit <$> lit <|>
      _PatVar <$> varid <|>
      mark "pattern"

join :: (Syntax f, Domain f s) => f (a s) -> (Prism (a s) (Annotated s a, b), f b) -> f (a s)
join p (_P, q) = Prism f g <$> annotated p <*> optional q <|> unparseable p where
  f (_ :< p, Nothing) = p
  f (p, Just q)       = construct _P (p, q)
  g x = case destruct _P x of
    Just (x, y) -> Just (x, Just y)
    Nothing     -> Nothing

left :: forall f a s. (Syntax f, Domain f s) => Prism (a s) (Annotated s a, Annotated s a) -> f (a s) -> f (a s)
left _P p = Prism f g <$> annotated p <*> many (annotated p) <|> unparseable p where
  f (_ :< p, []) = p
  f (p, q:qs)    = fold p q qs
  fold p q []     = construct _P (p, q)
  fold p q (r:rs) = fold (combine (empty :: f Void) (construct _P) (p, q)) r rs
  g x = case destruct _P x of
    Just (x, y) -> Just (x, unfold y)
    Nothing     -> Nothing
  unfold x = case destruct _P (view value x) of
    Just (x, y) -> x : unfold y
    Nothing     -> [x]

kind :: (Syntax f, Domain f s) => f (Kind s)
kind = kind0 `join` (_KindFun, reservedOp "->" *> annotated kind) <|> mark "kind" where
  kind0 = _KindType <$> reservedCon "Type" <|>
          _KindConstraint <$> reservedCon "Constraint" <|>
          _KindRecord <$> record '[' (annotated kind) ']' <|>
          special '(' *> kind <* special ')' <|>
          mark "kind(0)"

ty :: (Syntax f, Domain f s) => f (Type s)
ty = ty1 `join` (_TyFun, reservedOp "->" *> annotated ty) <|> mark "type" where
  ty1 = left _TyApply ty0 <|> mark "type(1)"
  ty0 = _TyVar <$> varid <|>
        _TyCon <$> conid <|>
        _TyRecord <$> record '(' (annotated ty) ')' <|>
        _TyPack <$> record '[' (annotated ty) ']' <|>
        mark "type(0)"

exp :: (Syntax f, Domain f s) => f (Exp s)
exp = exp3 `join` (_Sig, reservedOp ":" *> annotated ty) <|> mark "exp" where
  exp3 = _Mixfix <$> some (annotated (_TOp <$> qvarsym <|> _TExp <$> annotated exp2)) <|> mark "exp(3)"
  exp2 = _Read <$> reservedId "read" *> varid <*> reservedId "in" *> annotated exp <|>
         _Do <$> reservedId "do" *> block (annotated stmt) <|>
         _Case <$> reservedId "case" *> annotated exp <*> reservedId "of" *> block alt <|>
         _Cases <$> reservedId "cases" *> block alt <|>
         exp1 <|> mark "exp(2)"
  exp1 = left _Apply exp0 <|> mark "exp(1)"
  exp0 = _Record <$> record '(' (annotated exp) ')' <|>
         _Var <$> varid <|>
         _Lit <$> lit <|>
         mark "exp(0)"

stmt :: (Syntax f, Domain f s) => f (Stmt s)
stmt = _StmtDecl <$> reservedId "let" *> annotated decl <|> _StmtExp <$> annotated exp

alt :: (Syntax f, Domain f s) => f (Annotated s Pat, Annotated s Exp)
alt = annotated pat <*> reservedOp "->" *> annotated exp
