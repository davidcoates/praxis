{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Check.Generate
  ( Generatable(..)
  ) where

import           AST
import           Check.AST
import           Check.Constraint
import           Check.System
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
import qualified Data.Set            as Set
import           Prelude             hiding (exp, log, read)

class Show b => Generatable a b | a -> b where
  generate' :: a -> Praxis b
  generate  :: a -> Praxis b
  generate p = save stage $ do
    set stage Generate
    p' <- generate' p
    log Debug p'
    cs <- get (system . constraints)
    let cs' = nub . sort $ cs
    logList Debug cs
    return p'

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
parallel :: [Praxis a] -> Praxis [a]
parallel []     = return []
parallel [x]    = (:[]) <$> x
parallel (x:xs) = do
  (a, as) <- join x (parallel xs)
  return (a:as)

program :: Parse.Annotated Program -> Praxis (Annotated Program)
program (s :< p) = case p of

  Program ds -> do
    ds' <- traverse decl ds
    -- TODO remove from tEnv
    -- TODO check there aren't side effects
    return $ (Nothing, Nothing, s) :< Program ds'

typAs :: Parse.Annotated Type -> Kind -> Praxis (Kinded Type)
typAs t@(s :< _) k = do
  t' <- typ t
  require $ newDerivation (EqKind (tag t') k) (Custom "typAs: TODO") s
  return t'

qtypAs :: Parse.Annotated QType -> Kind -> Praxis (Kinded QType)
qtypAs q@(s :< _) k = do
  q' <- qtyp q
  let r = Custom "qtypeAs: TODO"
      c = case q' of
          (k' :< Forall _ _ t) -> requireAll $ [newDerivation (EqKind k' k) r s, newDerivation (EqKind (tag t) k) r s]
          _ -> pure ()
  return q'

qimpure :: Parse.Annotated (Impure QType) -> Praxis (Kinded QType, Kinded Type)
qimpure (_ :< t :# e) = do
  t' <- qtypAs t KindType
  e' <- typAs e KindEffect
  return (t', e')

impure :: Parse.Annotated (Impure Type) -> Praxis (Kinded Type, Kinded Type)
impure (_ :< t :# e) = do
  t' <- typAs t KindType
  e' <- typAs e KindEffect
  return (t', e')

qtyp :: Parse.Annotated QType -> Praxis (Kinded QType)
qtyp (s :< t) = case t of

  Mono t -> do
    k :< t <- typ (s :< t)
    return (k :< Mono t)

  Forall _ _ _ -> undefined -- FIXME


typ :: Parse.Annotated Type -> Praxis (Kinded Type)
typ (s :< t) = case t of

  TyApply f a -> do
    kb <- freshUniK
    f' <- typ f
    a' <- typ a
    let kf = tag f'
        ka = tag a'
    require $ newDerivation (EqKind kf (KindFun ka kb)) AppType s
    return (kb :< TyApply f' a')

  TyEffects es -> do
    es' <- traverse typ (Set.toList es)
    requireAll $ map (\(k :< _) -> newDerivation (EqKind k KindEffect) (Custom "typ: TyEffects TODO") s) es'
    -- TODO Need to flatten effects, or only during unification?
    return (KindEffect :< TyEffects (Set.fromList es'))

  TyCon n -> do
    e <- KEnv.lookup n
    case e of Nothing -> throwError (CheckError (NotInScope n s))
              Just k  -> return (k :< TyCon n)

  TyPack r -> do -- This one is easy
    r' <- traverse typ r
    return (KindRecord (fmap tag r') :< TyPack r')

  TyRecord r -> do -- TODO Need to check they're all pure ?
    r' <- traverse typ r
    requireAll $ map (\(k :< _) -> newDerivation (EqKind k KindType) (Custom "typ: TyRecord TODO") s) (map snd (Record.toList r'))
    return (KindType :< TyRecord r')

  TyVar v -> do
    e <- KEnv.lookup v
    case e of
      Just k -> return (k :< TyVar v)
      Nothing -> do
        k <- freshUniK
        KEnv.intro v k
        return (k :< TyVar v)

  _ -> error ("typ: " ++ show (s :< t))


-- TODO move this somewhere
fun :: Kinded Type -> Kinded Type -> Kinded Type -> Kinded Type
fun at bt be = let kt = KindRecord (Record.triple KindType KindType KindEffect)
                in KindType :< TyApply (KindFun kt KindType :< TyCon "->") (kt :< TyPack (Record.triple at bt be))

decl :: Parse.Annotated Decl -> Praxis (Annotated Decl)
decl (s :< d) = case d of

  -- TODO safe recursion check
  -- TODO check no duplicate variables
  DeclVar n ut e -> do

    -- TODO if polymorphic, de shoud be empty. How can we guarantee this?
    (dq, de) <- case ut of Nothing -> liftA2 (,) freshUniQ freshUniE
                           Just s  -> qimpure s

    -- TODO if user supplied a monomorphic type, we could just insert it here
    intro n dq

    dt <- freshUniT

    e' <- exp e
    let (et, ee) = tyef e'
    equalT dt et (UserSignature (Just n)) s -- TODO UserSignature isn't a great name for this ut is Nothing
    equalT de ee (UserSignature (Just n)) s
    require $ newDerivation (dq `Generalises` dt) (Generalisation n)  s

    return ((Nothing, Just ee, s) :< DeclVar n Nothing e')


stmt :: Parse.Annotated Stmt -> Praxis (Annotated Stmt, Int)
stmt (s :< x) = case x of

  StmtDecl d -> do
    d' <- decl d
    return ((Nothing, Just (ef d'), s) :< StmtDecl d', 1)

  StmtExp e -> do
    e' <- exp e
    let (et, ee) = tyef e'
    return ((Just et, Just ee, s) :< StmtExp e', 0)


kind :: Kinded Type -> Kind
kind = tag

effs :: [Kinded Type] -> Kinded Type
effs [] = KindEffect :< TyEffects Set.empty
effs (e : es) = let
  e' = case e of { _ :< TyEffects es -> es ; _ -> Set.singleton e }
  _ :< TyEffects es' = effs es
  in KindEffect :< TyEffects (Set.union e' es')

exp :: Parse.Annotated Exp -> Praxis (Annotated Exp)
exp (s :< e) = (\((t, e) :< x) -> ((Just t, Just e, s) :< x)) <$> case e of

  Apply f x -> do
    yt <- freshUniT
    ye <- freshUniE
    f' <- exp f
    x' <- exp x
    let (ft, fe) = tyef f'
    let (xt, xe) = tyef x'
    require $ newDerivation (EqType ft (fun xt yt ye)) AppFun s
    let e = effs [fe, xe, ye]
    return ((yt, e) :< Apply f' x')

  Case x alts -> do
    x' <- exp x
    let (xt, e1) = tyef x'
    alts' <- parallel (map bind alts)
    t1 <- equalTs (map (\((Just t, _, s) :< _, _) -> (t, s)) alts') CaseCongruence
    (t2, e2) <- equalIs (map (\(_, (Just t, Just e, s) :< _) -> (t, e, s)) alts') CaseCongruence
    require $ newDerivation (EqType xt t1) CaseCongruence s -- TODO probably should pick a better name for this
    return ((xt, effs [e1, e2]) :< Case x' alts')

  Cases alts -> closure $ do
    alts' <- parallel (map bind alts)
    t1 <- equalTs (map (\((Just t, _, s) :< _, _) -> (t, s)) alts') CaseCongruence
    (t2, e) <- equalIs (map (\(_, (Just t, Just e, s) :< _) -> (t, e, s)) alts') CaseCongruence
    return ((fun t1 t2 e, effs []) :< Cases alts')

  Do ss -> do
    (ss', i) <- traverseSum stmt ss
    let (Just t, _, _) = tag (last ss')
    let e = effs $ concatMap (\s -> case tag s of { (_, Just e, _) -> [e]; _ -> [] }) ss'
    elimN i
    return ((t, e) :< Do ss')

  If a b c -> do
    a' <- exp a
    (b', c') <- join (exp b) (exp c)
    let (at, ae) = tyef a'
    let (bt, be) = tyef b'
    let (ct, ce) = tyef c'
    require $ newDerivation (EqType at (KindType :< TyCon "Bool")) IfCondition s
    require $ newDerivation (EqType bt ct) IfCongruence s
    let e = effs [ae, be, ce]
    return ((bt, e) :< If a' b' c')

  Lambda p e -> closure $ do
    (p', i) <- pat p
    e' <- exp e
    elimN i
    let pt       = ty p'
    let (et, ee) = tyef e'
    return ((fun pt et ee, effs []) :< Lambda p' e')

  Lit x -> do
    let t = case x of { Int _ -> TyCon "Int" ; Bool _ -> TyCon "Bool" ; String _ -> TyCon "String" ; Char _ -> TyCon "Char" }
    -- TODO poly literals
    return ((KindType :< t, effs []) :< Lit x)

  Read n a -> do
    t <- read s n
    intro n (mono t)
    a' <- exp a
    elim
    return (tyef a' :< value a')

  Record r -> do
    r' <- traverse exp r
    let e = effs (map (ef . snd) (Record.toList r'))
    let t = KindType :< TyRecord (fmap ty r')
    return ((t, e) :< Record r')

{-
  Sig e t -> do
    e' <- exp e
    t <- impure t
    equalI t (ty e') (UserSignature Nothing) s
    return e'
-}

  Var n -> do
    t <- use s n
    return ((t, effs []) :< Var n)


equalT :: Kinded Type -> Kinded Type -> Reason -> Source -> Praxis ()
equalT t1 t2 r s = require $ newDerivation (EqType t1 t2) r s

equalTs :: [(Kinded Type, Source)] -> Reason -> Praxis (Kinded Type)
equalTs ((t, _):ts) r = sequence [equalT t t' r s | (t', s) <- ts] >> return t

equalIs :: [(Kinded Type, Kinded Type, Source)] -> Reason -> Praxis (Kinded Type, Kinded Type)
equalIs ts r = do
  t <- equalTs (map (\(t, _, s) -> (t, s)) ts) r
  let e = effs $ map (\(_, e, _) -> e) ts
  return (t, e)

bind :: (Parse.Annotated Pat, Parse.Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
bind (s :< p, e) = do
  (p', i) <- pat (s :< p)
  e' <- exp e
  elimN i
  return (p', e')

pat :: Parse.Annotated Pat -> Praxis (Annotated Pat, Int)
pat (s :< p) = (\(t :< x, i) -> ((Just t, Nothing, s) :< x, i)) <$> case p of

  PatAt v p -> do
    (p', i) <- pat p
    let t = ty p'
    intro v (mono t)
    return (t :< PatAt v p', i + 1)

  PatHole -> do
    t <- freshUniT
    return (t :< PatHole, 0)

  PatLit l -> return ((KindType :< TyCon (lit l)) :< PatLit l, 0)
    where lit (Bool _)   = "Bool"
          lit (Char _)   = "Char"
          lit (Int _)    = "Int"
          lit (String _) = "String"

  PatRecord r -> do
    (r', i) <- traverseSum pat r
    let t = KindType :< TyRecord (fmap ty r')
    return (t :< PatRecord r', i)

  PatVar v -> do
    t <- freshUniT
    intro v (mono t)
    return (t :< PatVar v, 1)


traverseSum :: (Applicative f, Traversable t) => (a -> f (b, Int)) -> t a -> f (t b, Int)
traverseSum f xs = (\x -> (fmap fst x, sum $ fmap snd x)) <$> traverse f xs
