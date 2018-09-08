{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Check.Generate
  ( Generatable(..)
  ) where

import           AST
import           Check.AST
import           Check.Constraint
import           Common              (traverseM)
import qualified Env.KEnv            as KEnv
import           Env.TEnv
import           Error
import           Inbuilts            hiding (ty)
import qualified Parse.Parse.AST     as Parse
import           Praxis
import           Record
import           Source
import           Tag
import           Type                hiding (getEffects)

import           Control.Applicative (liftA2)
import           Data.Foldable       (foldlM)
import           Data.List           (nub, sort, transpose)
import           Data.Monoid         (Sum (..))
import qualified Data.Set            as Set
import           Prelude             hiding (exp, log, read)

class Show b => Generatable a b | a -> b where
  generate' :: a -> Praxis (b, [Derivation])
  generate  :: a -> Praxis (b, [Derivation])
  generate p = save stage $ save inClosure $ do
    set stage Generate
    set inClosure False
    (p', cs) <- generate' p
    log Debug p'
    let cs' = nub . sort $ cs
    logList Debug cs'
    return (p', cs')

instance Generatable (Parse.Annotated Program) (Annotated Program) where
  generate' = program

instance Generatable (Parse.Annotated Exp) (Annotated Exp) where
  generate' = exp

instance Generatable (Parse.Annotated Type) (Kinded Type) where
  generate' = typ

tyef :: Annotated a -> (Kinded Type, Kinded Type)
tyef ((Just t, Just e, _) :< _) = (t, e)

ty :: Annotated a -> Kinded Type
ty ((Just t, _, _) :< _) = t

ef :: Annotated a -> Kinded Type
ef ((_, Just e, _) :< _) = e

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
    -- TODO check there aren't side effects
    return ((Nothing, Nothing, s) :< Program ds', cs)

typAs :: Parse.Annotated Type -> Kind -> Praxis (Kinded Type, [Derivation])
typAs t@(s :< _) k = do
  (t', c1) <- typ t
  let c2 = [newDerivation (EqKind (tag t') k) (Custom "typAs: TODO") s]
  return (t', c1 ++ c2)

qtypAs :: Parse.Annotated QType -> Kind -> Praxis (Kinded QType, [Derivation])
qtypAs q@(s :< _) k = do
  (q', c1) <- qtyp q
  return (q', c1 ++ f q')
    where r = Custom "qtypeAs: TODO"
          f q' = case q' of
            (k' :< Forall _ _ t) -> [ newDerivation (EqKind k' k) r s, newDerivation (EqKind (tag t) k) r s ]
            _ -> []

qimpure :: Parse.Annotated (Impure QType) -> Praxis (Kinded QType, Kinded Type, [Derivation])
qimpure (_ :< t :# e) = do
  (t', c1) <- qtypAs t KindType
  (e', c2) <- typAs e KindEffect
  return (t', e', c1 ++ c2)

impure :: Parse.Annotated (Impure Type) -> Praxis (Kinded Type, Kinded Type, [Derivation])
impure (_ :< t :# e) = do
  (t', c1) <- typAs t KindType
  (e', c2) <- typAs e KindEffect
  return (t', e', c1 ++ c2)

qtyp :: Parse.Annotated QType -> Praxis (Kinded QType, [Derivation])
qtyp (s :< t) = case t of

  Mono t -> do
    (k :< t, c) <- typ (s :< t)
    return (k :< Mono t, c)

  Forall _ _ _ -> undefined -- FIXME


typ :: Parse.Annotated Type -> Praxis (Kinded Type, [Derivation])
typ (s :< t) = case t of

  TyApply f a -> do
    kb <- freshUniK
    (f', c1) <- typ f
    (a', c2) <- typ a
    let kf = tag f'
        ka = tag a'
        c3 = [ newDerivation (EqKind kf (KindFun ka kb)) AppType s ]
    return (kb :< TyApply f' a', c1 ++ c2 ++ c3) -- TODO think about the order of constraints

  TyEffects es -> do
    (es', c1) <- traverseM typ (Set.toList es)
    let c2 = map (\(k :< _) -> newDerivation (EqKind k KindEffect) (Custom "typ: TyEffects TODO") s) es'
    -- TODO Need to flatten effects, or only during unification?
    return (KindEffect :< TyEffects (Set.fromList es'), c1 ++ c2)

  TyCon n -> do
    e <- KEnv.lookup n
    case e of Nothing -> throwError (CheckError (NotInScope n s))
              Just k  -> return (k :< TyCon n, [])

  TyPack r -> do -- This one is easy
    (r', c1) <- traverseM typ r
    return (KindRecord (fmap tag r') :< TyPack r', c1)

  TyRecord r -> do -- TODO Need to check they're all pure ?
    (r', c1) <- traverseM typ r
    let c2 = map (\(k :< _) -> newDerivation (EqKind k KindType) (Custom "typ: TyRecord TODO") s) (map snd (Record.toList r'))
    return (KindType :< TyRecord r', c1 ++ c2)

  TyVar v -> do
    e <- KEnv.lookup v
    case e of
      Just k -> return (k :< TyVar v, [])
      Nothing -> do
        k <- freshUniK
        KEnv.intro v k
        return (k :< TyVar v, [])

  _ -> error ("typ: " ++ show (s :< t))


-- TODO move this somewhere
fun :: Kinded Type -> Kinded Type -> Kinded Type -> Kinded Type
fun at bt be = let kt = KindRecord (Record.triple KindType KindType KindEffect)
                in KindType :< TyApply (KindFun kt KindType :< TyCon "->") (kt :< TyPack (Record.triple at bt be))

decl :: Parse.Annotated Decl -> Praxis (Annotated Decl, [Derivation])
decl (s :< d) = case d of

  -- TODO allow polymorpishm
  -- TODO safe recursion check
  -- TODO check no duplicate variables
  DeclVar n ut e -> do

    (dq, de, c1) <- case ut of Nothing -> liftA2 (\(k:<t) e -> (k :< Mono t, e, [])) freshUniT freshUniE
                               Just s  -> qimpure s

    intro n dq

    -- TODO allow checking of polymorphic functions
    let (k :< Mono t) = dq
    let dt = k :< t

    (e', c2) <- exp e
    let (et, ee) = tyef e'
    -- let c3 = equalT dt et (UserSignature (Just n)) s
    let c3 = [] -- FIXME
    let c4 = equalT de ee (UserSignature (Just n)) s
    return ((Nothing, Just ee, s) :< DeclVar n Nothing e', c1 ++ c2 ++ c3 ++ c4)


stmt :: Parse.Annotated Stmt -> Praxis (Annotated Stmt, ([Derivation], Sum Int))
stmt (s :< x) = case x of

  StmtDecl d -> do
    (d', c1) <- decl d
    return ((Nothing, Just (ef d'), s) :< StmtDecl d', (c1, Sum 1))

  StmtExp e -> do
    (e', c1) <- exp e
    let (et, ee) = tyef e'
    return ((Just et, Just ee, s) :< StmtExp e', (c1, Sum 0))


kind :: Kinded Type -> Kind
kind = tag

effs :: [Kinded Type] -> Kinded Type
effs [] = KindEffect :< TyEffects Set.empty
effs (e : es) = let
  e' = case e of { _ :< TyEffects es -> es ; _ -> Set.singleton e }
  _ :< TyEffects es' = effs es
  in KindEffect :< TyEffects (Set.union e' es')

exp :: Parse.Annotated Exp -> Praxis (Annotated Exp, [Derivation])
exp (s :< e) = (\((t, e) :< x, cs) -> ((Just t, Just e, s) :< x, cs)) <$> case e of

  Apply f x -> do
    yt <- freshUniT
    ye <- freshUniE
    (f', c1) <- exp f
    (x', c2) <- exp x
    let (ft, fe) = tyef f'
    let (xt, xe) = tyef x'
    let c3 = [ newDerivation (EqType ft (fun xt yt ye)) AppFun s ]
    let e = effs [fe, xe, ye]
    return ((yt, e) :< Apply f' x', c1 ++ c2 ++ c3)

  Cases alts -> do
    (alts', c1) <- parallel (map bind alts)
    let (t1, c2) = equalTs (map (\((Just t, _, s) :< _, _) -> (t, s)) alts') CaseCongruence
    let (t2, e, c3) = equalIs (map (\(_, (Just t, Just e, s) :< _) -> (t, e, s)) alts') CaseCongruence
    return ((fun t1 t2 e, effs []) :< Cases alts', c1 ++ c2)

  Do ss -> do
    (ss', (cs, Sum i)) <- traverseM stmt ss
    let (Just t, _, _) = tag (last ss')
    let e = effs $ concatMap (\s -> case tag s of { (_, Just e, _) -> [e]; _ -> [] }) ss'
    elimN i
    return ((t, e) :< Do ss', cs)

  If a b c -> do
    (a', c1) <- exp a
    ((b', c2), (c', c3)) <- join (exp b) (exp c)
    let (at, ae) = tyef a'
    let (bt, be) = tyef b'
    let (ct, ce) = tyef c'
    let c4 = [ newDerivation (EqType at (KindType :< TyCon "Bool")) IfCondition s, newDerivation (EqType bt ct) IfCongruence s ]
    let e = effs [ae, be, ce]
    return ((bt, e) :< If a' b' c', c1 ++ c2 ++ c3 ++ c4)

  Lambda p e -> do
    (p', Sum i) <- pat p
    (e', cs) <- save inClosure $ set inClosure True >> exp e -- FIXME
    elimN i
    let pt       = ty p'
    let (et, ee) = tyef e'
    return ((fun pt et ee, effs []) :< Lambda p' e', cs)

  Lit x -> do
    let t = case x of { Int _ -> TyCon "Int" ; Bool _ -> TyCon "Bool" ; String _ -> TyCon "String" ; Char _ -> TyCon "Char" }
    -- TODO poly literals
    return ((KindType :< t, effs []) :< Lit x, [])

  Read n a -> do
    (t, c1) <- read s n
    intro n (mono t)
    (a', c2) <- exp a
    elim
    return (tyef a' :< value a', c1 ++ c2)

  Record r -> do
    (r', c1) <- traverseM exp r
    let e = effs (map (ef . snd) (Record.toList r'))
    let t = KindType :< TyRecord (fmap ty r')
    return ((t, e) :< Record r', c1)

{-
  Sig e t -> do
    (e', c1) <- exp e
    (t, c3) <- impure t
    let c2 = equalI t (ty e') (UserSignature Nothing) s
    return (e', c1 ++ c2 ++ c3)
-}

  Var n -> do
    (t, c1) <- use s n
    return ((t, effs []) :< Var n, c1)


equalT :: Kinded Type -> Kinded Type -> Reason -> Source -> [Derivation]
equalT t1 t2 r s = [newDerivation (EqType t1 t2) r s]

equalTs :: [(Kinded Type, Source)] -> Reason -> (Kinded Type, [Derivation])
equalTs ((t, _):ts) r = (t, concat [equalT t t' r s | (t', s) <- ts])

equalIs :: [(Kinded Type, Kinded Type, Source)] -> Reason -> (Kinded Type, Kinded Type, [Derivation])
equalIs ts r = (t, e, cs)
  where (t, cs) = equalTs (map (\(t, _, s) -> (t, s)) ts) r
        e = effs $ map (\(_, e, _) -> e) ts


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

-- Always returns empty effects
pat :: Parse.Annotated Pat -> Praxis (Annotated Pat, Sum Int)
pat (s :< p) = (\(t :< x, i) -> ((Just t, Nothing, s) :< x, i)) <$> case p of

  PatAt v p -> do
    (p', Sum i) <- pat p
    let t = ty p'
    intro v (mono t)
    return (t :< PatAt v p', Sum $ i + 1)

  PatHole -> do
    t <- freshUniT
    return (t :< PatHole, Sum 0)

  PatLit l -> return ((KindType :< TyCon (lit l)) :< PatLit l, Sum 0)
    where lit (Bool _)   = "Bool"
          lit (Char _)   = "Char"
          lit (Int _)    = "Int"
          lit (String _) = "String"

  PatRecord r -> do
    (r', i) <- traverseM pat r
    let t = KindType :< TyRecord (fmap ty r')
    return (t :< PatRecord r', i)

  PatVar v -> do
    t <- freshUniT
    intro v (mono t)
    return (t :< PatVar v, Sum 1)

