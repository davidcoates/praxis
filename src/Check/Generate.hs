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

ty :: Annotated a -> Kinded Impure
ty ((Just t, _) :< _) = t

getPure (_ :< p :# e) = p
getEffects (_ :< p :# e) = e

split :: Kinded Impure -> (Kinded Type, Kinded Type)
split t = (getPure t, getEffects t)

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

impure :: Parse.Annotated Impure -> Praxis (Kinded Impure, [Derivation])
impure (s :< t :# e) = do
  (t', c1) <- typ t
  (e', c2) <- typ e
  let c3 = [ newDerivation (EqKind (tag t') KindType) (Custom "impure: TODO") s
           , newDerivation (EqKind (tag e') KindEffect) (Custom "impure: TODO") s
           ]
  return (KindType :< t' :# e', c1 ++ c2 ++ c3)

equalI :: Kinded Impure -> Kinded Impure -> Reason -> Source -> [Derivation]
equalI (_ :< t1 :# e1) (_ :< t2 :# e2) r s = [ newDerivation (EqType t1 t2) r s, newDerivation (EqType e1 e2) r s ]

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
fun :: Kinded Type -> Kinded Impure -> Kinded Type
fun ap bt = let kp = KindRecord (Record.triple KindType KindType KindEffect)
                (bp, be) = split bt
             in KindType :< TyApply (KindFun kp KindType :< TyCon "->") (kp :< TyPack (Record.triple ap bp be))

decl :: Parse.Annotated Decl -> Praxis (Annotated Decl, [Derivation])
decl (s :< d) = case d of

  -- TODO allow polymorpishm
  -- TODO safe recursion check
  DeclVar n ut e -> do

    (dt, c1) <- case ut of Nothing -> (\t -> (t, [])) <$> freshUniI
                           Just t  -> impure t

    intro n (mono (getPure dt))
    (e', c2) <- exp e
    let c3 = equalI dt (ty e') (UserSignature (Just n)) s
    return ((Just dt, s) :< DeclVar n Nothing e', c1 ++ c2 ++ c3)
    -- TODO why don't we return the type in DeclVar?


stmt :: Parse.Annotated Stmt -> Praxis (Annotated Stmt, ([Derivation], Sum Int))
stmt (s :< x) = case x of

  -- TODO should decl have a type in it?
  StmtDecl d -> do
    (d', c1) <- decl d
    return ((Just (ty d'), s) :< StmtDecl d', (c1, Sum 1))

  StmtExp e -> do
    (e', c1) <- exp e
    return ((Just (ty e'), s) :< StmtExp e', (c1, Sum 0))


kind :: Kinded Type -> Kind
kind = tag

effs :: [Kinded Type] -> Kinded Type
effs [] = KindEffect :< TyEffects Set.empty
effs (e : es) = let
  e' = case e of { _ :< TyEffects es -> es ; _ -> Set.singleton e }
  _ :< TyEffects es' = effs es
  in KindEffect :< TyEffects (Set.union e' es')


(#) :: Kinded Type -> Kinded Type -> Kinded Impure
t # e = KindType :< t :# e
-- TODO need to check t ~ KindType and e ~ KindEffect before calling this? Or is that already done?

exp :: Parse.Annotated Exp -> Praxis (Annotated Exp, [Derivation])
exp (s :< e) = case e of

  Apply f x -> do
    yt <- freshUniI
    let (yp, ye) = split yt
    (f', c1) <- exp f
    (x', c2) <- exp x
    let (fp, fe) = split $ ty f'
    let (xp, xe) = split $ ty x'
    let c3 = [ newDerivation (EqType fp (fun xp yt)) AppFun s ]
    let e = effs [fe, xe, ye]
    return ((Just (yp # e), s) :< Apply f' x', c1 ++ c2 ++ c3)

  Cases alts -> do
    (alts', c1) <- parallel (map bind alts)
    let (p, c2) = equalPs (map (\((Just t, s) :< _, _) -> (getPure t,s)) alts') CaseCongruence
    let (t, c3) = equalIs (map (\(_, (Just t, s) :< _) -> (t,s)) alts') CaseCongruence
    return ((Just (fun p t # effs []), s) :< Cases alts', c1 ++ c2)

  Do ss -> do
    (ss', (cs, Sum i)) <- traverseM stmt ss
    let es = effs $ map (getEffects . ty) ss'
    let t = getPure $ ty (last ss')
    elimN i
    return ((Just (t # es), s) :< Do ss', cs)

  If a b c -> do
    (a', c1) <- exp a
    ((b', c2), (c', c3)) <- join (exp b) (exp c)
    let (ap, ae) = split $ ty a'
    let (bp, be) = split $ ty b'
    let (cp, ce) = split $ ty c'
    let c4 = [ newDerivation (EqType ap (KindType :< TyCon "Bool")) IfCondition s, newDerivation (EqType bp cp) IfCongruence s ]
    let e = effs [ae, be, ce]
    return ((Just (bp # e), s) :< If a' b' c', c1 ++ c2 ++ c3 ++ c4)

  Lambda p e -> do
    (p', Sum i) <- pat p
    (e', cs) <- save inClosure $ set inClosure True >> exp e
    elimN i
    let t = fun (getPure $ ty p') (ty e')
    return ((Just (t # effs []), s) :< Lambda p' e', cs)

  Lit x -> do
    let p = case x of { Int _ -> TyCon "Int" ; Bool _ -> TyCon "Bool" ; String _ -> TyCon "String" ; Char _ -> TyCon "Char" }
    -- TODO poly literals
    return ((Just ((KindType :< p) # effs []), s) :< Lit x, [])

  Read n a -> do
    (p, c1) <- read s n
    intro n (mono p)
    (a', c2) <- exp a
    return (a', c1 ++ c2)

  Record r -> do
    (r', c1) <- traverseM exp r
    let e = effs (map (getEffects . ty . snd) (Record.toList r'))
    let p = KindType :< TyRecord (fmap (\t -> getPure (ty t)) r')
    return ((Just (p # e), s) :< Record r', c1)

  Sig e t -> do
    (e', c1) <- exp e
    (t, c3) <- impure t
    let c2 = equalI t (ty e') (UserSignature Nothing) s
    return (e', c1 ++ c2 ++ c3)

  Var n -> do
    (p, c1) <- use s n
    return ((Just (p # effs []), s) :< Var n, c1)


equalIs :: [(Kinded Impure, Source)] -> Reason -> (Kinded Impure, [Derivation])
equalIs [(t, _)]    _ = (t, [])
equalIs ((t, s):ts) r = let (t', c1) = equalIs ts r
                            (p,   e) = split t
                            (p', e') = split t'
                            c2 = [ newDerivation (EqType p p') r s ]
                         in (p # effs [e, e'], c1 ++ c2)

-- TODO remove duplication here
equalPs :: [(Kinded Type, Source)] -> Reason -> (Kinded Type, [Derivation])
equalPs [(p, _)]    _ = (p, [])
equalPs ((p, s):ps) r = let (p', cs) = equalPs ps r
                            c = newDerivation (EqType p p') r s
                             in (p, c:cs)


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
pat (s :< p) = case p of

  PatAt v p -> do
    (p', Sum i) <- pat p
    let t = getPure $ ty p'
    intro v (mono t)
    return ((Just (t # effs []), s) :< PatAt v p', Sum $ i + 1)

  PatHole -> do
    t <- freshUniP
    return ((Just (t # effs []), s) :< PatHole, Sum 0)

  PatLit l -> return ((Just ((KindType :< TyCon (lit l)) # effs []), s) :< PatLit l, Sum 0)
    where lit (Bool _)   = "Bool"
          lit (Char _)   = "Char"
          lit (Int _)    = "Int"
          lit (String _) = "String"

  PatRecord r -> do
    (r', i) <- traverseM pat r
    let t = KindType :< TyRecord (fmap (getPure . ty) r')
    return ((Just (t # effs []), s) :< PatRecord r', i)
    -- TODO check no duplicate variables? Perhaps not here - in decl instead?

  PatVar v -> do
    t <- freshUniP
    intro v (mono t)
    return ((Just (t # effs []), s) :< PatVar v, Sum 1)

