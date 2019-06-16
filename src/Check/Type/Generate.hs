{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Type.Generate
  ( generate
  ) where

import           Check.Type.Reason
import           Check.Type.Require
import           Check.Type.System
import           Common
import qualified Env.KEnv            as KEnv
import           Env.TEnv
import           Introspect
import           Praxis
import           Print
import           Record
import           Stage
import           Term

import           Control.Applicative (liftA2)
import           Data.Foldable       (foldlM)
import           Data.List           (nub, sort, transpose)
import qualified Data.Set            as Set
import           Prelude             hiding (exp, log, read)

ty :: Typed a -> Annotation TypeAnn a
ty = view annotation

generate :: Recursive a => Kinded a -> Praxis (Typed a)
generate x = save stage $ do
  stage .= TypeCheck Generate
  x' <- visit gen x
  output x'
  cs <- use (our . constraints)
  output $ separate "\n\n" (nub . sort $ cs)
  return x'

gen :: Recursive a => Kinded a -> Visit Praxis (Annotation TypeAnn a) (Typed a)
gen x = case typeof x of
  IDataAlt -> skip
  IDecl    -> Resolve (decl x)
  IExp     -> Resolve (exp x)
  IProgram -> skip
  IQType   -> Resolve (pure (cast x))
  IType    -> Resolve (pure (cast x))

-- Computes in 'parallel' (c.f. `sequence` which computes in series)
-- For our purposes we require each 'branch' to start with the same type environment TODO kEnv etc
-- The output environments are all contextJoined
parallel :: [Praxis a] -> Praxis [a]
parallel []     = return []
parallel [x]    = (:[]) <$> x
parallel (x:xs) = do
  (a, as) <- join x (parallel xs)
  return (a:as)

-- TODO move this somewhere
fun :: Typed Type -> Typed Type -> Typed Type
fun a b = TyFun a b `as` phantom KindType

equal :: Typed Type -> Typed Type -> Reason -> Source -> Praxis ()
equal t1 t2 r s = require $ newConstraint (t1 `TEq` t2) r s

decl :: Kinded Decl -> Praxis (Typed Decl)
decl = split $ \s -> \case

  -- TODO safe recursion check
  -- TODO check no duplicate variables
  DeclVar n sig e -> do
    t <- case sig of Nothing -> (\t -> (view source t, ()) :< Mono t) <$> freshUniT
                     Just t  -> pure (cast t)
    intro n t
    e' <- exp e
    -- TODO this won't work if we allow nested polymorphic definitions
    let t' = case view value t of { Mono t -> t; Forall _ t -> t }
    equal t' (ty e') (UserSignature (Just n)) s
    return (() :< DeclVar n Nothing e')


stmt :: Kinded Stmt -> Praxis (Typed Stmt)
stmt = split $ \s -> \case

  StmtDecl d -> do
    d' <- decl d
    return (() :< StmtDecl d')

  StmtExp e -> do
    e' <- exp e
    return (() :< StmtExp e')


mono :: Typed Type -> Typed QType
mono t = (view source t, ()) :< Mono t

exp :: Kinded Exp -> Praxis (Typed Exp)
exp = split $ \s -> \case

  Apply f x -> do
    yt <- freshUniT
    ye <- freshUniT
    f' <- exp f
    x' <- exp x
    let ft = ty f'
    let xt = ty x'
    require $ newConstraint (ft `TEq` fun xt yt) AppFun s
    return (yt :< Apply f' x')

  Case x alts -> do
    x' <- exp x
    let xt = ty x'
    alts' <- parallel (map bind alts)
    t1 <- equals (map (view tag . fst) alts') CaseCongruence
    t2 <- equals (map (view tag . snd) alts') CaseCongruence
    require $ newConstraint (xt `TEq` t1) CaseCongruence s -- TODO probably should pick a better name for this
    return (xt :< Case x' alts')

  Cases alts -> closure $ do
    alts' <- parallel (map bind alts)
    t1 <- equals (map (view tag . fst) alts') CaseCongruence
    t2 <- equals (map (view tag . snd) alts') CaseCongruence
    return (fun t1 t2 :< Cases alts')

  Do ss -> do
    ss' <- traverse stmt ss
    let f (StmtDecl _) = 1
        f (StmtExp _)  = 0
    elimN (sum (map (f . view value) ss'))
    let t = (\(_ :< StmtExp ((_, t) :< _)) -> t) (last ss')
    return (t :< Do ss')

  If a b c -> do
    a' <- exp a
    (b', c') <- join (exp b) (exp c)
    require $ newConstraint (ty a' `TEq` TyCon "Bool" `as` phantom KindType) IfCondition s
    require $ newConstraint (ty b' `TEq` ty c') IfCongruence s
    return (ty b' :< If a' b' c')

  Lambda p e -> closure $ do
    (i, p') <- pat p
    e' <- exp e
    elimN i
    return (fun (ty p') (ty e') :< Lambda p' e')

  Lit x -> do
    let t = case x of { Int _ -> TyCon "Int" ; Bool _ -> TyCon "Bool" ; String _ -> TyCon "String" ; Char _ -> TyCon "Char" }
    return (t `as` phantom KindType :< Lit x)

  Read n e -> do
    t <- read s n
    intro n (mono t)
    e' <- exp e
    elim
    return (ty e' :< view value e')

  Record r -> do
    r' <- traverse exp r
    let t = TyRecord (fmap ty r') `as` phantom KindType
    return (t :< Record r')

{-
  Sig e t -> do
    e' <- exp e
    t <- impure t
    equalI t (ty e') (UserSignature Nothing) s
    return e'
-}

  Var n -> do
    t <- mark s n
    return (t :< Var n)

equals :: [(Source, Typed Type)] -> Reason -> Praxis (Typed Type)
equals ((_, t):ts) r = sequence [equal t t' r s | (s, t') <- ts] >> return t

bind :: (Kinded Pat, Kinded Exp) -> Praxis (Typed Pat, Typed Exp)
bind (s :< p, e) = do
  (i, p') <- pat (s :< p)
  e' <- exp e
  elimN i
  return (p', e')


pat :: Kinded Pat -> Praxis (Int, Typed Pat)
pat = splitPair $ \s -> \case

  PatAt v p -> do
    (i, p') <- pat p
    let t = ty p'
    intro v (mono t)
    return (i + 1, t :< PatAt v p')

  PatHole -> do
    t <- freshUniT
    return (0, t :< PatHole)

  PatLit l -> return (0, TyCon (lit l) `as` phantom KindType :< PatLit l)
    where lit (Bool _)   = "Bool"
          lit (Char _)   = "Char"
          lit (Int _)    = "Int"
          lit (String _) = "String"

  PatRecord r -> do
    (Sum i, r') <- traverse (over first Sum) <$> traverse pat r
    let t = TyRecord (fmap ty r') `as` phantom KindType
    return (i, t :< PatRecord r')

  PatVar v -> do
    t <- freshUniT
    intro v (mono t)
    return (1, t :< PatVar v)
