{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Type.Generate
  ( generate
  ) where

import           AST
import           Check.Type.Annotate
import           Check.Type.Constraint
import           Check.Type.Require
import           Check.Type.System
import           Common
import qualified Env.KEnv              as KEnv
import           Env.TEnv
import           Error
import           Introspect
import           Parse.Annotate        (Parsed)
import           Praxis
import           Record
import           Stage
import           Type

import           Control.Applicative   (liftA2)
import           Data.Foldable         (foldlM)
import           Data.List             (nub, sort, transpose)
import qualified Data.Set              as Set
import           Prelude               hiding (exp, log, read)

-- TODO factor out (Phantom, ()) everywhere?

ty :: Typed a -> Annotation TypeCheck a
ty = view annotation

throwCheckError r = throwError (CheckError r)

generate :: Recursive a => Parsed a -> Praxis (Typed a)
generate x = save stage $ do
  stage .= TypeCheck Generate
  x' <- introspect gen x
  -- log Debug x'
  -- cs <- use (our . constraints)
  -- logList Debug (nub . sort $ cs)
  return x'

gen :: Recursive a => Parsed a -> Intro Praxis TypeCheck a
gen x = case typeof x of
  IDataAlt -> Notice (pure ())
  IDecl    -> Realise (decl x)
  IExp     -> Realise (exp x)
  IProgram -> Notice (pure ())
  IQType   -> Notice (pure ())
  IType    -> Notice (pure ())

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
fun a b = let
  sa = view source a
  sb = view source b
  s = (sa <> sb) { spelling = spelling sa ++ " -> " ++ spelling sb } in
  (s, ()) :< TyApply ((s, ()) :< TyCon "->") ((s, ()) :< TyPack (Record.pair a b))

equal :: Typed Type -> Typed Type -> Reason -> Source -> Praxis ()
equal t1 t2 r s = require $ newConstraint (t1 `Eq` t2) r s

split :: ((Source, a Parse) -> Praxis (Annotation TypeCheck a, a TypeCheck)) -> Parsed a -> Praxis (Typed a)
split f x = do
  (a', x') <- f (view source x, view value x)
  return ((view source x, a') :< x')

splitFree :: ((Source, a Parse) -> Praxis (Annotation TypeCheck a, a TypeCheck, b)) -> Parsed a -> Praxis (Typed a, b)
splitFree f x = do
  (a', x', b) <- f (view source x, view value x)
  return ((view source x, a') :< x', b)

cast :: Recursive a => Parsed a -> Typed a
cast = runIdentity . introspect f where
  f :: Recursive a => Parsed a -> Intro Identity TypeCheck a
  f x = case typeof x of
    IType  -> Notice (Identity (view annotation x))
    IQType -> Notice (Identity (view annotation x))

-- TODO call this something else, move it somewhere common, perhaps Type
empty :: Typed Type
empty = (Phantom, ()) :< TyFlat Set.empty

-- TODO Source
flat :: [Typed Type] -> Typed Type
flat ts = (Phantom, ()) :< TyFlat (Set.unions (map f ts)) where
  f (_ :< TyFlat ts) = ts
  f t                = Set.singleton t

decl :: Parsed Decl -> Praxis (Typed Decl)
decl = split $ \(s, d) -> case d of

  -- TODO safe recursion check
  -- TODO check no duplicate variables
  DeclVar n sig e -> do

    -- TODO if polymorphic, de shoud be empty. Is this guaranteed?
    dq <- case sig of Nothing -> freshUniQ
                      Just t  -> pure (cast t)

    -- TODO if user supplied a monomorphic type, we could just insert it here
    intro n dq

    dt <- freshUniT

    e' <- exp e
    equal dt (ty e') (UserSignature (Just n)) s -- TODO UserSignature isn't a great name for this ut is Nothing
    require $ newConstraint (dq `Generalises` dt) (Generalisation n) s

    return ((), DeclVar n Nothing e')

stmt :: Parsed Stmt -> Praxis (Typed Stmt, Maybe (Typed Type))
stmt = splitFree $ \(s, x) -> case x of

  StmtDecl d -> do
    d' <- decl d
    return ((), StmtDecl d', Nothing)

  StmtExp e -> do
    e' <- exp e
    return ((), StmtExp e', Just (ty e'))


mono :: Typed Type -> Typed QType
mono t = view tag t :< Mono t

exp :: Parsed Exp -> Praxis (Typed Exp)
exp = split $ \(s, e) -> case e of

  Apply f x -> do
    yt <- freshUniT
    ye <- freshUniT
    f' <- exp f
    x' <- exp x
    let ft = ty f'
    let xt = ty x'
    require $ newConstraint (ft `Eq` fun xt yt) AppFun s
    return (yt, Apply f' x')

  Case x alts -> do
    x' <- exp x
    let xt = ty x'
    alts' <- parallel (map bind alts)
    t1 <- equals (map (view tag . fst) alts') CaseCongruence
    t2 <- equals (map (view tag . snd) alts') CaseCongruence
    require $ newConstraint (xt `Eq` t1) CaseCongruence s -- TODO probably should pick a better name for this
    return (xt, Case x' alts')

  Cases alts -> closure $ do
    alts' <- parallel (map bind alts)
    t1 <- equals (map (view tag . fst) alts') CaseCongruence
    t2 <- equals (map (view tag . snd) alts') CaseCongruence
    return (fun t1 t2, Cases alts')

  Do ss -> do
    let f Nothing = 0
        f _       = 1
    (ss', i) <- traverseSum (\x -> over second f <$> stmt x) ss
    (_, Just t) <- stmt (last ss)
    elimN i
    return (t, Do ss')

  If a b c -> do
    a' <- exp a
    (b', c') <- join (exp b) (exp c)
    require $ newConstraint (ty a' `Eq` ((Phantom, ()) :< TyCon "Bool")) IfCondition s
    require $ newConstraint (ty b' `Eq` ty c') IfCongruence s
    return (ty b', If a' b' c')

  Lambda p e -> closure $ do
    (p', i) <- pat p
    e' <- exp e
    elimN i
    return (fun (ty p') (ty e'), Lambda p' e')

  Lit x -> do
    let t = case x of { Int _ -> TyCon "Int" ; Bool _ -> TyCon "Bool" ; String _ -> TyCon "String" ; Char _ -> TyCon "Char" }
    return ((Phantom, ()) :< t, Lit x)

  Read n e -> do
    t <- read s n
    intro n (mono t)
    e' <- exp e
    elim
    return (ty e', view value e')

  Record r -> do
    r' <- traverse exp r
    let t = (Phantom, ()) :< TyRecord (fmap ty r')
    return (t, Record r')

{-
  Sig e t -> do
    e' <- exp e
    t <- impure t
    equalI t (ty e') (UserSignature Nothing) s
    return e'
-}

  Var n -> do
    t <- mark s n
    return (t, Var n)

equals :: [(Source, Typed Type)] -> Reason -> Praxis (Typed Type)
equals ((_, t):ts) r = sequence [equal t t' r s | (s, t') <- ts] >> return t

bind :: (Parsed Pat, Parsed Exp) -> Praxis (Typed Pat, Typed Exp)
bind (s :< p, e) = do
  (p', i) <- pat (s :< p)
  e' <- exp e
  elimN i
  return (p', e')

pat :: Parsed Pat -> Praxis (Typed Pat, Int)
pat = splitFree $ \(s, p) -> case p of

  PatAt v p -> do
    (p', i) <- pat p
    let t = ty p'
    intro v (mono t)
    return (t, PatAt v p', i + 1)

  PatHole -> do
    t <- freshUniT
    return (t, PatHole, 0)

  PatLit l -> return (((Phantom, ()) :< TyCon (lit l)), PatLit l, 0)
    where lit (Bool _)   = "Bool"
          lit (Char _)   = "Char"
          lit (Int _)    = "Int"
          lit (String _) = "String"

  PatRecord r -> do
    (r', i) <- traverseSum pat r
    let t = (Phantom, ()) :< TyRecord (fmap ty r')
    return (t, PatRecord r', i)

  PatVar v -> do
    t <- freshUniT
    intro v (mono t)
    return (t, PatVar v, 1)


traverseSum :: (Applicative f, Traversable t) => (a -> f (b, Int)) -> t a -> f (t b, Int)
traverseSum f xs = (\x -> (fmap fst x, sum $ fmap snd x)) <$> traverse f xs

