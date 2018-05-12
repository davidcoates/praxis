module Check.Generate
  ( generate
  ) where

import qualified Parse.Parse.AST as Parse

import Check.Derivation
import Check.Env
import Check.AST
import Source
import AST
import Type
import Tag
import Control.Exception.Base (assert)
import Inbuilts hiding (ty)
import Compiler
import Error
import Record

import Control.Monad (foldM)

contextJoin :: Source -> Env -> Env -> Env -> (Env, [Derivation])
contextJoin _ [] [] [] = ([],[])
contextJoin s ((x,(xt,xi)):xs) ((y,(yt,yi)):ys) ((z,(zt,zi)):zs) =
  assert ((x,xt) == (y,yt) && (y,yt) == (z,zt)) r
  where (l, c1)  = ((x,(xt,max yi zi)), if (xi == yi) == (yi == zi) then [] else [newDerivation (dropC xt) "Env join" s])
        (ls, c2) = contextJoin s xs ys zs
        r = (l:ls, c1 ++ c2)

generate :: Compiler [Derivation]
generate = do
  set stage Generate
  p <- get desugaredAST
  l <- get tEnv
  (l', p', cs) <- gp (l, p)
  set tEnv l'
  set typedAST p'
  debugPrint p'
  debugPrint cs
  return cs

ty :: Annotated Exp -> (Pure, Effects)
ty ((Just (p :# e), _) :< _) = (p, e)

gParallel :: Source -> Env -> [Compiler (Env, a, [Derivation])] -> Compiler (Env, [a], [Derivation])
gParallel s l [x] = do
  (l1, a, c1) <- x
  return (l1, [a], c1)
gParallel s l (x:xs) = do
  (l1, a, c1) <- x
  (l2, as, c2) <- gParallel s l xs
  let (l3, c3) = contextJoin s l l1 l2
  return (l3, a:as, c1 ++ c2 ++ c3)

gFoldM :: ((Env, Parse.Annotated a) -> Compiler (Env, Annotated a, [Derivation])) -> Env -> [Parse.Annotated a] -> Compiler (Env, [Annotated a], [Derivation])
gFoldM _ l1 []     = pure (l1, [], [])
gFoldM f l1 (d:ds) = do
  (l2, d', c1)  <- f (l1, d)
  (l3, ds', c2) <- gFoldM f l2 ds
  return (l3, d':ds', c1 ++ c2)

gp :: (Env, Parse.Annotated Program) -> Compiler (Env, Annotated Program, [Derivation])
gp (l1, p) = ($ p) $ rec $ \s x -> case x of

  Program ds -> (\(l, ds, cs) -> (l, (Nothing, s) :< Program ds, cs)) <$> gFoldM gd l1 ds


gd :: (Env, Parse.Annotated Decl) -> Compiler (Env, Annotated Decl, [Derivation])
gd (l1, d) = ($ d) $ rec $ \s x -> case x of

  FunDecl n e -> do
    p <- freshUniP
    (l2, e', c1) <- ge (intro (n, p) l1, e) -- TODO need to check safety of recursive functions
    return (l2, (Just (p :# empty), s) :< FunDecl n e', c1)


ge :: (Env, Parse.Annotated Exp) -> Compiler (Env, Annotated Exp, [Derivation])
ge (l1, e) = ($ e) $ rec $ \s x -> case x of

  Lit x -> do
    let p = litTy x -- TODO polymorphic literals
    return (l1, (Just (p :# empty), s) :< Lit x, [])

  If a b c -> do
    (l2, a', c1) <- ge (l1, a)
    (l3, b', c2) <- ge (l2, b)
    (l3', c', c3) <- ge (l2, c)
    let (l4, c4) = contextJoin s l2 l3 l3'
    let (ap, ae) = ty a'
    let (bp, be) = ty b'
    let (cp, ce) = ty c'
    let c5 = [ newDerivation (EqualP ap (TyPrim TyBool)) "condition of if expression must be Bool" s, newDerivation (EqualP bp cp) "branches of if expression must have the same type" s ]
    let e = unions [ae, be, ce]
    return (l4, (Just (bp :# e), s) :< If a' b' c', c1 ++ c2 ++ c3 ++ c4 ++ c5)

  Var n -> do
    (p, l2, c1) <- use s n l1
    return (l2, (Just (p :# empty), s) :< Var n, c1)

  Apply f x -> do
    yp :# ye  <- freshUniT
    (l2, f', c1) <- ge (l1, f)
    (l3, x', c2) <- ge (l2, x)
    let (fp, fe) = ty f'
    let (xp, xe) = ty x'
    let c3 = [ newDerivation (EqualP fp (TyFun xp (yp :# ye))) "fun app" s ]
    let e = unions [fe, xe, ye]
    return (l3, (Just (yp :# e), s) :< Apply f' x', c1 ++ c2 ++ c3)

  Let n a b -> do
    (l2, a', c1) <- ge (l1, a)
    let (ap, ae) = ty a'
    (l3, b', c2) <- ge (intro (n, ap) l2, b)
    let (l4, c3) = elim s l3
    let (bp, be) = ty b'
    return (l4, (Just (bp :# unions [ae, be]), s) :< Let n a' b', c1 ++ c2 ++ c3)

  LetBang n a -> do
    (p, c1) <- readUse s n l1
    (l2, a', c2) <- ge (intro (n, TyBang p) l1, a)
    return (l2, a', c1 ++ c2)

  Signature a (sp :# se) -> do
    (l2, a', c1) <- ge (l1, a)
    let (ap, ae) = ty a'
    let c2 = [ newDerivation (EqualP sp ap) "user-supplied signature" s, newDerivation (EqualE se ae) "user-supplied signature" s ]
    return (l2, a', c1 ++ c2)

  Lambda n e -> do
    np <- freshUniP
    (l2, e', c1) <- ge (intro (n, np) l1, e)
    let (l3, c2) = elim s l2
    let (ep, ee) = ty e'
    return (l3, (Just (TyFun np (ep :# ee) :# empty), s) :< Lambda n e', c1 ++ c2)

  Case e alts -> do
    (l2, e', c1) <- ge (l1, e)
    (l3, alts', c2) <- gParallel s l2 (map (\a -> gbind (l2, a)) alts)
    let (t, c3) = tParallel (map (\(_, (Just t, s) :< _) -> (t,s)) alts')
    return (l3, (Just t, s) :< Case e' alts', c1 ++ c2 ++ c3)

  Unit -> return (l1, (Just (TyUnit :# empty), s) :< Unit, [])

  Record r -> do
    (l2, es, c1) <- gFoldM ge l1 (map snd (toList r))
    let r' = Record.fromList (zip (map fst (toList r)) es)
    let e = unions (map (snd . ty) es)
    let p = TyRecord (fmap (fst . ty) r')
    return (l2, (Just (p :# e), s) :< Record r', c1)

tParallel :: [(Type, Source)] -> (Type, [Derivation])
tParallel [(t, _)] = (t, [])
tParallel ((p :# e, s):ts) = let (p' :# e', cs) = tParallel ts
                                 c = newDerivation (EqualP p p') "case alternatives must have the same type" s
                             in (p :# unions [e, e'], c:cs)

gbind :: (Env, (Parse.Annotated Pat, Parse.Annotated Exp)) -> Compiler (Env, (Annotated Pat, Annotated Exp), [Derivation])
gbind (l1, (s :< p,e)) = do
  (l2, p', i) <- gpat (l1, s :< p)
  (l3, e', c1) <- ge (l2, e)
  let (l4, c2) = elimN i s l3
  return (l4, (p', e'), c1 ++ c2)

gpat :: (Env, Parse.Annotated Pat) -> Compiler (Env, Annotated Pat, Int)
gpat (l1, p) = ($ p) $ rec $ \s x -> case x of

  PatUnit -> return (l1, (Just (TyUnit :# empty), s) :< PatUnit, 0)

  PatLit l -> return (l1, (Just (TyPrim (tyLit l) :# empty), s) :< PatLit l,  0)
    where tyLit (Int _) = TyInt
          tyLit (Bool _) = TyBool
          tyLit (Char _) = TyChar
          tyLit (String _) = TyString

  PatVar v -> do
    vp <- freshUniP
    return (intro (v, vp) l1, (Just (vp :# empty), s) :< PatVar v, 1)
 
{- |Captures e returns a list of all free variables in e.
   This is used to ensure functions don't capture linear variables.
   There is a slight difference between captures and used free variables,
   specifically for read-only references.
   E.g., In "let x! in y", only y is used, but both x and y are captured.
-}
captures :: Exp a -> [Name]
captures = undefined
