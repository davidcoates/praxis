module Check.Generate
  ( generate
  ) where

import AST
import Check.Derivation
import Check.AST
import Common (traverseM)
import Compiler
import Env.TEnv
import Error
import Inbuilts hiding (ty)
import qualified Parse.Parse.AST as Parse
import Record
import Source
import Type
import Tag

import Data.Foldable (foldlM)
import Data.List (transpose)
import Data.Monoid (Sum(..))
import Prelude hiding (read, exp)

-- TODO data for constraint reasons?
generate :: Compiler [Derivation]
generate = save stage $ save inClosure $ do
  set stage Generate
  set inClosure False
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
parallel :: [Compiler (a, [Derivation])] -> Compiler ([a], [Derivation])
parallel []     = return ( [], [])
parallel [x]    = (\(a, cs) -> ([a], cs)) <$> x
parallel (x:xs) = do
  ((a, c1), (as, c2)) <- join x (parallel xs)
  return (a:as, c1 ++ c2)

program :: Parse.Annotated Program -> Compiler (Annotated Program, [Derivation])
program (s :< p) = case p of

  Program ds -> do
    (ds', cs) <- traverseM decl ds
    -- TODO remove from tEnv
    return ((Nothing, s) :< Program ds', cs)


decl :: Parse.Annotated Decl -> Compiler (Annotated Decl, [Derivation])
decl (s :< d) = case d of

  -- TODO tidy this up
  DeclFun n t i as -> do

    if i == 0 then do
      -- Special case, the binding is not a function (and is non-recursive)
      let [([], e)] = as
      (e', c1) <- exp e
      let t' = ty e'
      intro n (getPure t')
      let c2 = case t of Just t  -> equalT t t' "user-supplied signature TODO" s
                         Nothing -> []
      return ((Just t', s) :< DeclFun n t i [([], e')], c1 ++ c2)
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
    (alts', c2) <- parallel (map bind alts)
    let (t, c3) = equalTs (map (\(_, (Just t, s) :< _) -> (t,s)) alts') "case alternatives must have the same type"
    return ((Just t, s) :< Case e' alts', c1 ++ c2 ++ c3)

  Do ss -> do
    (ss', (cs, Sum i)) <- traverseM stmt ss
    let es = unions $ map (getEffects . ty) ss'
    let t = ty (last ss')
    elimN i
    return ((Just t, s) :< Do ss', cs)

  If a b c -> do
    (a', c1) <- exp a
    ((b', c2), (c', c3)) <- join (exp b) (exp c)
    let ap :# ae = ty a'
    let bp :# be = ty b'
    let cp :# ce = ty c'
    let c4 = [ newDerivation (EqualP ap (TyPrim TyBool)) "condition of if expression must be Bool" s, newDerivation (EqualP bp cp) "branches of if expression must have the same type" s ]
    let e = unions [ae, be, ce]
    return ((Just (bp :# e), s) :< If a' b' c', c1 ++ c2 ++ c3 ++ c4)

  Lambda p e -> do
    (p', Sum i) <- pat p
    let t :# _ = ty p'
    (e', cs) <- save inClosure $ set inClosure True >> exp e
    let tp :# te = ty e'
    elimN i
    return ((Just (TyFun t (tp :# te) :# empty), s) :< Lambda p' e', cs)

  Lit x -> do
    let p = litTy x -- TODO polymorphic literals
    return ((Just (p :# empty), s) :< Lit x, [])

  Read n a -> do
    (p, c1) <- read s n
    intro n (TyBang p)
    (a', c2) <- exp a
    return (a', c1 ++ c2)

  Record r -> do
    (r', c1) <- traverseM exp r
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
  ((ps', e'), cs) <- save inClosure $ set inClosure True >> binds (ps, e)
  elimN i
  return ((p':ps', e'), cs)

bind :: (Parse.Annotated Pat, Parse.Annotated Exp) -> Compiler ((Annotated Pat, Annotated Exp), [Derivation])
bind (s :< p, e) = do
  (p', Sum i) <- pat (s :< p)
  (e', cs) <- exp e
  elimN i
  return ((p', e'), cs)


pat :: Parse.Annotated Pat -> Compiler (Annotated Pat, Sum Int)
pat (s :< p) = case p of

  PatAt v p -> do
    (p', Sum i) <- pat p
    vp <- freshUniP
    intro v vp
    return ((Just (vp :# empty), s) :< PatAt v p', Sum $ i + 1)

  PatHole -> do
    vp <- freshUniP
    return ((Just (vp :# empty), s) :< PatHole, Sum 0)

  PatLit l -> return ((Just (TyPrim (tyLit l) :# empty), s) :< PatLit l,  Sum 0)
    where tyLit (Bool _)   = TyBool
          tyLit (Char _)   = TyChar
          tyLit (Int _)    = TyInt
          tyLit (String _) = TyString

  PatRecord r -> do
    (r', i) <- traverseM pat r
    let p = TyRecord (fmap (getPure . ty) r')
    return ((Just (p :# empty), s) :< PatRecord r', i)
    -- TODO check no duplicate variables? Perhaps not here - in decl instead?

  PatVar v -> do
    vp <- freshUniP
    intro v vp
    return ((Just (vp :# empty), s) :< PatVar v, Sum 1)

