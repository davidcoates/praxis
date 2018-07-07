{-# LANGUAGE FlexibleContexts #-}

module Check.Generate
  ( Generatable(..)
  ) where

import           AST
import           Check.AST
import           Check.Derivation
import           Common           (traverseM)
import           Env.TEnv
import           Error
import           Inbuilts         hiding (ty)
import qualified Parse.Parse.AST  as Parse
import           Praxis
import           Record
import           Source
import           Tag
import           Type             hiding (getEffects)

import           Data.Foldable    (foldlM)
import           Data.List        (nub, sort, transpose)
import           Data.Monoid      (Sum (..))
import           Prelude          hiding (exp, log, read)

class Show (Annotated a) => Generatable a where
  generate' :: Parse.Annotated a -> Praxis (Annotated a, [Derivation])
  generate  :: Parse.Annotated a -> Praxis (Annotated a, [Derivation])
  generate p = save stage $ save inClosure $ do
    set stage Generate
    set inClosure False
    (p', cs) <- generate' p
    log Debug p'
    let cs' = nub . sort $ cs
    logList Debug cs'
    return (p', cs')

instance Generatable Program where
  generate' = program

instance Generatable Exp where
  generate' = exp

-- TODO Consider moving these or renaming these or using lenses
getPure :: Impure -> Pure
getPure (p :# _) = p

getEffects :: Impure -> Effects
getEffects (_ :# e) = e

ty :: Annotated a -> Impure
ty ((Just t, _) :< _) = t

-- Computes in 'parallel' (c.f. `sequence` which computes in series)
-- For our purposes we require each 'branch' to start with the same type environment TODO kEnv etc
-- The output environments are all contextJoined
parallel :: [Praxis (a, [Derivation])] -> Praxis ([a], [Derivation])
parallel []     = return ( [], [])
parallel [x]    = (\(a, cs) -> ([a], cs)) <$> x
parallel (x:xs) = do
  ((a, c1), (as, c2)) <- join x (parallel xs)
  return (a:as, c1 ++ c2)

program :: Parse.Annotated Program -> Praxis (Annotated Program, [Derivation])
program (s :< p) = case p of

  Program ds -> do
    (ds', cs) <- traverseM decl ds
    -- TODO remove from tEnv
    return ((Nothing, s) :< Program ds', cs)

decl :: Parse.Annotated Decl -> Praxis (Annotated Decl, [Derivation])
decl (s :< d) = case d of

  -- TODO tidy this up, TODO allow polymorpishm
  DeclFun n ut i as -> do

    dt <- case ut of Nothing -> freshUniI
                     Just t  -> return t

    if i == 0 then do
      -- Special case, the binding is not a function (and is non-recursive)
      let [([], e)] = as
      (e', c1) <- exp e
      let t' = ty e'
      intro n (Mono dt)
      let c2 = equalI dt t' (UserSignature (Just n)) s
      return ((Just dt, s) :< DeclFun n ut i [([], e')], c1 ++ c2)
    else do
      -- TODO clean this up
      intro n (Mono dt)
      as' <- mapM binds as
      let c1 = concatMap snd as'
      let bs = map fst as'
      let tss = map (\ps -> equalIs (map (\((Just t, s) :< _) -> (t,s)) ps) Unknown) . transpose . map fst $ bs
      let ts = map fst tss
      let c2 = concatMap snd tss
      let es = map snd bs
      let (te, c3) = equalIs (map (\((Just t, s) :< _) -> (t,s)) es) Unknown
      let t' = fold ts te
      let c4 = equalI dt t' (UserSignature (Just n)) s
      return ((Just dt, s) :< DeclFun n ut i bs, c1 ++ c2 ++ c3 ++ c4)
        where fold            [] te = te
              fold ((p :# _):ps) te = TyFun p (fold ps te) :# empty

stmt :: Parse.Annotated Stmt -> Praxis (Annotated Stmt, ([Derivation], Sum Int))
stmt (s :< x) = case x of

  -- TODO should decl have a type in it?
  StmtDecl d -> do
    (d', c1) <- decl d
    return ((Just (ty d'), s) :< StmtDecl d', (c1, Sum $ 1))

  StmtExp e -> do
    (e', c1) <- exp e
    return ((Just (ty e'), s) :< StmtExp e', (c1, Sum $ 0))


exp :: Parse.Annotated Exp -> Praxis (Annotated Exp, [Derivation])
exp (s :< e) = case e of

  Apply f x -> do
    yp :# ye  <- freshUniI
    (f', c1) <- exp f
    (x', c2) <- exp x
    let fp :# fe = ty f'
    let xp :# xe = ty x'
    let c3 = [ newDerivation (EqualP fp (TyFun xp (yp :# ye))) Application s ]
    let e = unions [fe, xe, ye]
    return ((Just (yp :# e), s) :< Apply f' x', c1 ++ c2 ++ c3)

  Case e alts -> do
    (e', c1) <- exp e
    (alts', c2) <- parallel (map bind alts)
    let (t, c3) = equalIs (map (\(_, (Just t, s) :< _) -> (t,s)) alts') CaseCongruence
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
    let c4 = [ newDerivation (EqualP ap (TyPrim TyBool)) IfCondition s, newDerivation (EqualP bp cp) IfCongruence s ]
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
    intro n (Mono (TyBang p :# empty))
    (a', c2) <- exp a
    return (a', c1 ++ c2)

  Record r -> do
    (r', c1) <- traverseM exp r
    let e = unions (map (getEffects . ty . snd) (Record.toList r'))
    let p = TyRecord (fmap (getPure . ty) r')
    return ((Just (p :# e), s) :< Record r', c1)

  Sig e t -> do
    (e', c1) <- exp e
    let c2 = equalI t (ty e') (UserSignature Nothing) s
    return (e', c1 ++ c2)

  Var n -> do
    (p, c1) <- use s n
    return ((Just (p :# empty), s) :< Var n, c1)


equalIs :: [(Impure, Source)] -> Reason -> (Impure, [Derivation])
equalIs [(t, _)]         _ = (t, [])
equalIs ((p :# e, s):ts) r = let (p' :# e', cs) = equalIs ts r
                                 c = newDerivation (EqualP p p') r s
                             in (p :# unions [e, e'], c:cs)

binds :: ([Parse.Annotated Pat], Parse.Annotated Exp) -> Praxis (([Annotated Pat], Annotated Exp), [Derivation])
binds ([], e) = do
  (e', c) <- exp e
  return (([], e'), c)
binds ((s :< p) : ps, e) = do
  (p', Sum i) <- pat (s :< p)
  ((ps', e'), cs) <- save inClosure $ set inClosure True >> binds (ps, e)
  elimN i
  return ((p':ps', e'), cs)

bind :: (Parse.Annotated Pat, Parse.Annotated Exp) -> Praxis ((Annotated Pat, Annotated Exp), [Derivation])
bind (s :< p, e) = do
  (p', Sum i) <- pat (s :< p)
  (e', cs) <- exp e
  elimN i
  return ((p', e'), cs)


pat :: Parse.Annotated Pat -> Praxis (Annotated Pat, Sum Int)
pat (s :< p) = case p of

  PatAt v p -> do
    (p', Sum i) <- pat p
    t <- freshUniP
    intro v (Mono (t :# empty))
    return ((Just (t :# empty), s) :< PatAt v p', Sum $ i + 1)

  PatHole -> do
    t <- freshUniP
    return ((Just (t :# empty), s) :< PatHole, Sum 0)

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
    t <- freshUniP
    intro v (Mono (t :# empty))
    return ((Just (t :# empty), s) :< PatVar v, Sum 1)

