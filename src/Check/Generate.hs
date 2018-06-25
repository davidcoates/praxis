module Check.Generate
  ( generate
  ) where

import qualified Parse.Parse.AST as Parse

import Check.Derivation
import Check.Env
import Check.AST
import Common (traverseF)
import Source
import AST
import Type
import Tag
import Control.Exception.Base (assert)
import Inbuilts hiding (ty)
import Compiler
import Error
import Record

import Data.Foldable (foldlM)

contextJoin :: Source -> Env -> Env -> Env -> Compiler [Derivation]
contextJoin s l lb1 lb2 = let (l', cs) = contextJoin' s l lb1 lb2 in set tEnv l' >> return cs
  where contextJoin' _ [] [] [] = ([],[])
        contextJoin' s ((x,(xt,xi)):xs) ((y,(yt,yi)):ys) ((z,(zt,zi)):zs) =
          assert ((x,xt) == (y,yt) && (y,yt) == (z,zt)) r
          where (l, c1)  = ((x,(xt,max yi zi)), if (xi == yi) == (yi == zi) then [] else [newDerivation (dropC xt) "Env join" s])
                (ls, c2) = contextJoin' s xs ys zs
                r = (l:ls, c1 ++ c2)

generate :: Compiler [Derivation]
generate = do
  set stage Generate
  p <- get desugaredAST
  (p', cs) <- gp p
  set typedAST p'
  debugPrint p'
  debugPrint cs
  return cs

ty :: Annotated a -> (Pure, Effects)
ty ((Just (p :# e), _) :< _) = (p, e)

gParallel :: Source -> [Compiler (a, [Derivation])] -> Compiler ([a], [Derivation])
gParallel s []     = return ([], [])
gParallel s (x:xs) = do
  l <- get tEnv
  (y,  c1) <- x
  lb1 <- get tEnv
  (ys, c2) <- gParallel s xs
  lb2 <- get tEnv
  c3 <- contextJoin s l lb1 lb2
  return (y:ys, c1 ++ c2 ++ c3)

gp :: Parse.Annotated Program -> Compiler (Annotated Program, [Derivation])
gp p = ($ p) $ rec $ \s x -> case x of

  Program ds -> do
    (ds', cs) <- traverseF gd ds
    return ((Nothing, s) :< Program ds', cs)


gd :: Parse.Annotated Decl -> Compiler (Annotated Decl, [Derivation])
gd d = ($ d) $ rec $ \s x -> case x of

  DeclFun n t i as -> undefined -- TODO FIXME
{- do
    p <- freshUniP
    intro n p
    (e', c1) <- ge e -- TODO need to check safety of recursive functions
    let (tp, te) = ty e'
    let c2 = [ newDerivation (EqualP p tp) "TODO" s, newDerivation (EqualE te empty) "top-level function must be pure" s]
    return ((Just (p :# empty), s) :< FunDecl n e', c1 ++ c2)
-}

ge :: (Parse.Annotated Exp) -> Compiler (Annotated Exp, [Derivation])
ge e = ($ e) $ rec $ \s x -> case x of

  Apply f x -> do
    yp :# ye  <- freshUniT
    (f', c1) <- ge f
    (x', c2) <- ge x
    let (fp, fe) = ty f'
    let (xp, xe) = ty x'
    let c3 = [ newDerivation (EqualP fp (TyFun xp (yp :# ye))) "fun app" s ]
    let e = unions [fe, xe, ye]
    return ((Just (yp :# e), s) :< Apply f' x', c1 ++ c2 ++ c3)

  Case e alts -> do
    (e', c1) <- ge e
    (alts', c2) <- gParallel s (map gbind alts)
    let (t, c3) = tParallel (map (\(_, (Just t, s) :< _) -> (t,s)) alts')
    return ((Just t, s) :< Case e' alts', c1 ++ c2 ++ c3)

  If a b c -> do
    (a', c1) <- ge a
    l <- get tEnv
    (b', c2) <- ge b
    lb1 <- get tEnv
    (c', c3) <- ge c
    lb2 <- get tEnv
    c4 <- contextJoin s l lb1 lb2
    let (ap, ae) = ty a'
    let (bp, be) = ty b'
    let (cp, ce) = ty c'
    let c5 = [ newDerivation (EqualP ap (TyPrim TyBool)) "condition of if expression must be Bool" s, newDerivation (EqualP bp cp) "branches of if expression must have the same type" s ]
    let e = unions [ae, be, ce]
    return ((Just (bp :# e), s) :< If a' b' c', c1 ++ c2 ++ c3 ++ c4 ++ c5)

  Lambda (_ :< PatVar n) e -> do -- TODO FIXME
    np <- freshUniP
    intro n np
    (e', c1) <- ge e
    c2 <- elim s
    let (ep, ee) = ty e'
    return ((Just (TyFun np (ep :# ee) :# empty), s) :< Lambda (undefined :< PatVar n) e', c1 ++ c2)

  Lit x -> do
    let p = litTy x -- TODO polymorphic literals
    return ((Just (p :# empty), s) :< Lit x, [])

  Read n a -> do
    (p, c1) <- readUse s n
    intro n (TyBang p)
    (a', c2) <- ge a
    return (a', c1 ++ c2)

  Record r -> do
    (r', c1) <- traverseF ge r
    let e = unions (map (snd . ty . snd) (Record.toList r'))
    let p = TyRecord (fmap (fst . ty) r')
    return ((Just (p :# e), s) :< Record r', c1)

  Sig a (sp :# se) -> do
    (a', c1) <- ge a
    let (ap, ae) = ty a'
    let c2 = [ newDerivation (EqualP sp ap) "user-supplied signature" s, newDerivation (EqualE se ae) "user-supplied signature" s ]
    return (a', c1 ++ c2)

  Var n -> do
    (p, c1) <- use s n
    return ((Just (p :# empty), s) :< Var n, c1)


tParallel :: [(Type, Source)] -> (Type, [Derivation])
tParallel [(t, _)] = (t, [])
tParallel ((p :# e, s):ts) = let (p' :# e', cs) = tParallel ts
                                 c = newDerivation (EqualP p p') "case alternatives must have the same type" s
                             in (p :# unions [e, e'], c:cs)

gbind :: (Parse.Annotated Pat, Parse.Annotated Exp) -> Compiler ((Annotated Pat, Annotated Exp), [Derivation])
gbind (s :< p, e) = do
  (p', i) <- gpat (s :< p)
  (e', c1) <- ge e
  c2 <- elimN i s
  return ((p', e'), c1 ++ c2)

gpat :: Parse.Annotated Pat -> Compiler (Annotated Pat, Int)
gpat p = ($ p) $ rec $ \s x -> case x of

  PatAt v p -> do
    (p', i) <- gpat p
    vp <- freshUniP
    intro v vp
    return ((Just (vp :# empty), s) :< PatAt v p', i + 1)

  PatHole -> do
    vp <- freshUniP
    intro "_" vp
    return ((Just (vp :# empty), s) :< PatHole, 1) -- TODO

  PatLit l -> return ((Just (TyPrim (tyLit l) :# empty), s) :< PatLit l,  0)
    where tyLit (Bool _)   = TyBool
          tyLit (Char _)   = TyChar
          tyLit (Int _)    = TyInt
          tyLit (String _) = TyString
  
  PatRecord r -> do
    let gpat' p = (\(p, i) -> (p, [i])) <$> gpat p -- TODO use Sum ?
    (r', is) <- traverseF gpat' r
    let p = TyRecord (fmap (fst . ty) r')
    return ((Just (p :# empty), s) :< PatRecord r', sum is)
    -- TODO check no duplicate variables? Perhaps not here - in decl instead?

  PatVar v -> do
    vp <- freshUniP
    intro v vp
    return ((Just (vp :# empty), s) :< PatVar v, 1)


{- |Captures e returns a list of all free variables in e.
   This is used to ensure functions don't capture linear variables.
   There is a slight difference between captures and used free variables,
   specifically for read-only references.
   E.g., In "let x! in y", only y is used, but both x and y are captured.
-}
captures :: Exp a -> [Name]
captures = undefined
