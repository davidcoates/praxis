module Check.Generate
  ( generate
  ) where

import Prelude hiding (exp)

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
import Data.List (transpose)
import Data.Monoid (Sum(..))

-- TODO data for constraint reasons?

contextJoin :: Source -> Env -> Env -> Env -> Compiler [Derivation]
contextJoin s l lb1 lb2 = let (l', cs) = contextJoin' s l lb1 lb2 in set tEnv l' >> return cs
  where contextJoin' _ [] [] [] = ([],[])
        contextJoin' s ((x,(xt,xi)):xs) ((y,(yt,yi)):ys) ((z,(zt,zi)):zs) =
          assert ((x,xt) == (y,yt) && (y,yt) == (z,zt)) r
          where (l, c1)  = ((x,(xt,max yi zi)), if (xi == yi) == (yi == zi) then [] else [newDerivation (dropC xt) "Env join" s])
                (ls, c2) = contextJoin' s xs ys zs
                r = (l:ls, c1 ++ c2)

generate :: Compiler [Derivation]
generate = setIn stage Generate $ setIn inClosure False $ do
  p <- get desugaredAST
  (p', cs) <- program p
  set typedAST p'
  debugPrint p'
  debugPrint cs
  return cs

-- TODO Consider moving these or renaming these or using lenses
getPure :: Type -> Pure
getPure (p :# _) = p

getEffects :: Type -> Effects
getEffects (_ :# e) = e

ty :: Annotated a -> Type
ty ((Just t, _) :< _) = t

-- Computes in 'parallel' (c.f. `sequence` which computes in series)
-- For our purposes we require each 'branch' to start with the same type environment TODO kEnv etc 
-- The output environments are all contextJoined
parallel :: Source -> [Compiler (a, [Derivation])] -> Compiler ([a], [Derivation])
parallel s []     = return ( [], [])
parallel s [x]    = (\(a, cs) -> ([a], cs)) <$> x
parallel s (x:xs) = do
  l <- get tEnv
  (y,  c1) <- x
  lb1 <- get tEnv
  set tEnv l
  (ys, c2) <- parallel s xs
  lb2 <- get tEnv
  c3 <- contextJoin s l lb1 lb2
  return (y:ys, c1 ++ c2 ++ c3)

program :: Parse.Annotated Program -> Compiler (Annotated Program, [Derivation])
program (s :< p) = case p of

  Program ds -> do
    (ds', cs) <- traverseF decl ds
    -- TODO remove from tEnv
    return ((Nothing, s) :< Program ds', cs)


decl :: Parse.Annotated Decl -> Compiler (Annotated Decl, [Derivation])
decl (s :< d) = case d of

  -- TODO tidy this up
  DeclFun n t i as -> do

    if i == 0 then do
      -- Special case, the binding is not a function (and is non-recursive)
      let [([], e)] = as
      (e', c) <- exp e
      let t' = ty e'
      intro n (getPure t')
      let c = case t of Just t  -> equalT t t' "user-supplied signature TODO" s
                        Nothing -> []
      return ((Just t', s) :< DeclFun n t i [([], e')], c)
    else do
      -- TODO clean this up
      p <- freshUniP
      intro n p
      as' <- mapM binds as
      let c1 = concat $ map snd as'
      let bs = map fst as'
      let tss = map (\ps -> equalTs (map (\((Just t, s) :< _) -> (t,s)) ps) "TODO") . transpose . map fst $ bs
      let ts = map fst tss
      let c2 = concat $ map snd tss
      let es = map snd $ bs
      let (te, c3) = equalTs (map (\((Just t, s) :< _) -> (t,s)) es) "TODO"
      let t'@(p' :# _) = fold ts te
      let c4 = [ newDerivation (EqualP p p') "TODO" s ]
      let c5 = case t of Just t  -> equalT t t' "user-supplied signature TODO" s
                         Nothing -> []
      return ((Just t', s) :< DeclFun n t i bs, c1 ++ c2 ++ c3 ++ c4 ++ c5)
        where fold            [] te = te
              fold ((p :# _):ps) te = TyFun p (fold ps te) :# empty

stmt :: Parse.Annotated Stmt -> Compiler (Annotated Stmt, ([Derivation], Sum Int))
stmt (s :< x) = case x of

  -- TODO should decl have a type in it?
  StmtDecl d -> do
    (d', c1) <- decl d
    return ((Just (ty d'), s) :< StmtDecl d', (c1, Sum $ 1))

  StmtExp e -> do
    (e', c1) <- exp e
    return ((Just (ty e'), s) :< StmtExp e', (c1, Sum $ 0))


exp :: Parse.Annotated Exp -> Compiler (Annotated Exp, [Derivation])
exp (s :< e) = case e of

  Apply f x -> do
    yp :# ye  <- freshUniT
    (f', c1) <- exp f
    (x', c2) <- exp x
    let fp :# fe = ty f'
    let xp :# xe = ty x'
    let c3 = [ newDerivation (EqualP fp (TyFun xp (yp :# ye))) "fun app" s ]
    let e = unions [fe, xe, ye]
    return ((Just (yp :# e), s) :< Apply f' x', c1 ++ c2 ++ c3)

  Case e alts -> do
    (e', c1) <- exp e
    (alts', c2) <- parallel s (map bind alts)
    let (t, c3) = equalTs (map (\(_, (Just t, s) :< _) -> (t,s)) alts') "case alternatives must have the same type"
    return ((Just t, s) :< Case e' alts', c1 ++ c2 ++ c3)

  Do ss -> do
    (ss', (c1, Sum i)) <- traverseF stmt ss
    let es = unions $ map (getEffects . ty) ss'
    let t = ty (last ss')
    c2 <- elimN i s
    return ((Just t, s) :< Do ss', c1 ++ c2)

  If a b c -> do
    (a', c1) <- exp a
    l <- get tEnv
    (b', c2) <- exp b
    lb1 <- get tEnv
    (c', c3) <- exp c
    lb2 <- get tEnv
    c4 <- contextJoin s l lb1 lb2
    let ap :# ae = ty a'
    let bp :# be = ty b'
    let cp :# ce = ty c'
    let c5 = [ newDerivation (EqualP ap (TyPrim TyBool)) "condition of if expression must be Bool" s, newDerivation (EqualP bp cp) "branches of if expression must have the same type" s ]
    let e = unions [ae, be, ce]
    return ((Just (bp :# e), s) :< If a' b' c', c1 ++ c2 ++ c3 ++ c4 ++ c5)

  Lambda p e -> do
    (p', Sum i) <- pat p
    let t :# _ = ty p'
    (e', c1) <- setIn inClosure True (exp e)
    let tp :# te = ty e'
    c2 <- elimN i s
    return ((Just (TyFun t (tp :# te) :# empty), s) :< Lambda p' e', c1 ++ c2)

  Lit x -> do
    let p = litTy x -- TODO polymorphic literals
    return ((Just (p :# empty), s) :< Lit x, [])

  Read n a -> do
    (p, c1) <- readUse s n
    intro n (TyBang p)
    (a', c2) <- exp a
    return (a', c1 ++ c2)

  Record r -> do
    (r', c1) <- traverseF exp r
    let e = unions (map (getEffects . ty . snd) (Record.toList r'))
    let p = TyRecord (fmap (getPure . ty) r')
    return ((Just (p :# e), s) :< Record r', c1)

  Sig e t -> do
    (e', c1) <- exp e
    let c2 = equalT t (ty e') "User-supplied signature" s
    return (e', c1 ++ c2)

  Var n -> do
    (p, c1) <- use s n
    return ((Just (p :# empty), s) :< Var n, c1)


equalTs :: [(Type, Source)] -> String -> (Type, [Derivation]) 
equalTs [(t, _)]         _ = (t, [])
equalTs ((p :# e, s):ts) m = let (p' :# e', cs) = equalTs ts m
                                 c = newDerivation (EqualP p p') m s
                             in (p :# unions [e, e'], c:cs)

binds :: ([Parse.Annotated Pat], Parse.Annotated Exp) -> Compiler (([Annotated Pat], Annotated Exp), [Derivation])
binds ([], e) = do
  (e', c) <- exp e
  return (([], e'), c)
binds ((s :< p) : ps, e) = do
  (p', Sum i) <- pat (s :< p)
  ((ps', e'), c1) <- setIn inClosure True $ binds (ps, e)
  c2 <- elimN i s
  return ((p':ps', e'), c1 ++ c2)

bind :: (Parse.Annotated Pat, Parse.Annotated Exp) -> Compiler ((Annotated Pat, Annotated Exp), [Derivation])
bind (s :< p, e) = do
  (p', Sum i) <- pat (s :< p)
  (e', c1) <- exp e
  c2 <- elimN i s
  return ((p', e'), c1 ++ c2)


pat :: Parse.Annotated Pat -> Compiler (Annotated Pat, Sum Int)
pat (s :< p) = case p of

  PatAt v p -> do
    (p', Sum i) <- pat p
    vp <- freshUniP
    intro v vp
    return ((Just (vp :# empty), s) :< PatAt v p', Sum $ i + 1)

-- TODO pat to return constraints for PatHole ?
  PatHole -> do
    vp <- freshUniP
    intro "_" vp
    return ((Just (vp :# empty), s) :< PatHole, Sum 1) -- TODO?

  PatLit l -> return ((Just (TyPrim (tyLit l) :# empty), s) :< PatLit l,  Sum 0)
    where tyLit (Bool _)   = TyBool
          tyLit (Char _)   = TyChar
          tyLit (Int _)    = TyInt
          tyLit (String _) = TyString
  
  PatRecord r -> do
    (r', i) <- traverseF pat r
    let p = TyRecord (fmap (getPure . ty) r')
    return ((Just (p :# empty), s) :< PatRecord r', i)
    -- TODO check no duplicate variables? Perhaps not here - in decl instead?

  PatVar v -> do
    vp <- freshUniP
    intro v vp
    return ((Just (vp :# empty), s) :< PatVar v, Sum 1)

