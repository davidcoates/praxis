{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Type.Generate
  ( generate
  ) where

import           Check.Error
import           Check.Type.Reason
import           Check.Type.Require
import           Check.Type.System
import           Common
import           Env
import qualified Env.LEnv           as LEnv
import           Introspect
import           Praxis
import           Pretty
import           Print
import           Record
import           Stage
import           Term

import           Control.Monad      (replicateM)
import           Data.Foldable      (foldlM)
import           Data.List          (nub, sort)
import qualified Data.Set           as Set
import           Prelude            hiding (exp, log, lookup, read)
import qualified Prelude            (lookup)

ty :: (Recursive a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
ty = annotation . just

{-
TODO, want to allow things like:
f : forall a. a -> a
f x = x : a -- This a refers to the a introduced by f

Which means we need some map from TyVars to TyUnis
So that in-scope TyVars can use subbed.

Alternative is to transform the source which would mess up error messages

OR don't allow this, and don't allow explicit forall.
-}
ungeneralise :: [Name] -> Praxis (Annotated Type -> Annotated Type)
ungeneralise vs = do
  l <- zipWith (\n (_ :< t) -> (n, t)) vs <$> replicateM (length vs) freshTyUni
  return $ sub (\case { TyVar n -> n `Prelude.lookup` l; _ -> Nothing})

ungeneraliseQType :: Annotated QType -> Praxis (Annotated Type)
ungeneraliseQType (_ :< t) = case t of
  Mono t      -> return t
  Forall vs t -> ($ t) <$> ungeneralise vs

join :: Praxis a -> Praxis b -> Praxis (a, b)
join f1 f2 = do
  l <- use tEnv
  x <- f1
  l1 <- use tEnv
  tEnv .= l
  y <- f2
  l2 <- use tEnv
  tEnv .= LEnv.join l1 l2
  return (x, y)

closure :: Praxis a -> Praxis a
closure x = do
  tEnv %= LEnv.push
  r <- x
  tEnv %= LEnv.pop
  return r

-- TODO reduce duplication here
read :: Source -> Name -> Praxis (Annotated Type)
read s n = do
  l <- use tEnv
  case LEnv.lookupFull n l of
    Just (c, u, t) -> do
      t <- ungeneraliseQType t
      requires [ newConstraint (Share t) (UnsafeView n) s | u ]
      requires [ newConstraint (Share t) (Captured n) s   | c ]
      return t
    Nothing     -> throwAt s (NotInScope n)

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
mark :: Source -> Name -> Praxis (Annotated Type)
mark s n = do
  l <- use tEnv
  case LEnv.lookupFull n l of
    Just (c, u, t) -> do
      tEnv .= LEnv.mark n l
      t <- ungeneraliseQType t
      requires [ newConstraint (Share t) (Shared n)   s | u ]
      requires [ newConstraint (Share t) (Captured n) s | c ]
      return t
    Nothing     -> throwAt s (NotInScope n)

getData :: Source -> Name -> Praxis DataAltInfo
getData s n = do
  l <- use daEnv
  case lookup n l of
    Just v  -> return (view (annotation . just) v)
    Nothing -> throwAt s $ "data constructor " <> quote (pretty n) <> " is not in scope"

generate :: Recursive a => Annotated a -> Praxis (Annotated a)
generate x = save stage $ do
  stage .= TypeCheck Generate
  x' <- generateImpl x
  output x'
  cs <- use (our . constraints)
  output $ separate "\n\n" (nub . sort $ cs)
  -- TODO show tEnv and daEnv
  return x'

generateImpl :: Recursive a => Annotated a -> Praxis (Annotated a)
generateImpl x = case typeof x of
    IDecl -> decl x
    IExp  -> exp x
    _     -> value (recurse generateImpl) x

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
fun :: Annotated Type -> Annotated Type -> Annotated Type
fun a b = TyFun a b `as` phantom KindType

apply :: Annotated Type -> [Annotated Type] -> Annotated Type
apply t []     = t
apply s (t:ts) = let KindFun k1 k2 = view value (view (annotation . just) s) in apply (TyApply s t `as` k2) ts -- To be kind-correct it must be KindFun

equal :: Annotated Type -> Annotated Type -> Reason -> Source -> Praxis ()
equal t1 t2 r s = require $ newConstraint (t1 `TEq` t2) r s

decl :: Annotated Decl -> Praxis (Annotated Decl)
decl = splitTrivial $ \s -> \case

  -- TODO Share constraints needed!
  DeclData n ps alts -> do
    -- TODO could be kind annotated to avoid this lookup
    Just k <- kEnv `uses` Env.lookup n
    let c = TyCon n `as` k
        f ((s, Nothing) :< DataAlt n args) = do
          let rt = apply c $ map (over value (\(TyPatVar n) -> TyVar n)) ps
              ns = map ((\(TyPatVar n) -> n) . view value) ps
              ct = phantom $ case ps of
                [] -> Mono rt
                _  -> Forall (map ((\(TyPatVar n) -> n) . view value) ps) (foldr fun rt args)
              da = ((s, Just (DataAltInfo ns ct args rt)) :< DataAlt n args)
          daEnv %= Env.intro n da
          return da
    alts' <- traverse f alts
    return $ DeclData n ps alts'

  -- TODO safe recursion check
  -- TODO check no duplicate variables
  DeclVar n sig e -> do
    t <- case sig of Nothing -> (\t -> (view source t, Nothing) :< Mono t) <$> freshTyUni
                     Just t  -> pure t
    tEnv %= intro n t
    e' <- exp e
    -- TODO this won't work if we allow nested polymorphic definitions
    let t' = case view value t of { Mono t -> t; Forall _ t -> t }
    equal t' (view ty e') (UserSignature (Just n)) s
    return $ DeclVar n Nothing e'


mono :: Annotated Type -> Annotated QType
mono t = (view source t, Nothing) :< Mono t

exp :: Annotated Exp -> Praxis (Annotated Exp)
exp = split $ \s -> \case

  Apply f x -> do
    yt <- freshTyUni
    f' <- exp f
    x' <- exp x
    let ft = view ty f'
    let xt = view ty x'
    require $ newConstraint (ft `TEq` fun xt yt) AppFun s
    return (yt :< Apply f' x')

  Case x alts -> do
    x' <- exp x
    let xt = view ty x'
    op <- freshTyOpUni
    alts' <- parallel (map (bind op) alts)
    t1 <- equals (map ((\t -> (view source t, view ty t)) . fst) alts') CaseCongruence
    t2 <- equals (map ((\t -> (view source t, view ty t)) . snd) alts') CaseCongruence
    require $ newConstraint (TyOp op xt `as` phantom KindType `TEq` t1) CaseCongruence s -- TODO probably should pick a better name for this
    return (t2 :< Case x' alts')

  Cases alts -> closure $ do
    op <- freshTyOpUni
    alts' <- parallel (map (bind op) alts)
    t1 <- equals (map ((\t -> (view source t, view ty t)) . fst) alts') CaseCongruence
    t2 <- equals (map ((\t -> (view source t, view ty t)) . snd) alts') CaseCongruence
    return (fun t1 t2 :< Cases alts')

  Con n -> do
    DataAltInfo _ q _ _ <- getData s n
    t <- ungeneraliseQType q
    return (t :< Con n)

  Do ss -> do
    ss' <- traverse generateImpl ss
    let f (StmtDecl _) = 1
        f (StmtExp _)  = 0
    tEnv %= elimN (sum (map (f . view value) ss'))
    let t = (\(_ :< StmtExp ((_, Just t) :< _)) -> t) (last ss')
    return (t :< Do ss')

  If a b c -> do
    a' <- exp a
    (b', c') <- join (exp b) (exp c)
    require $ newConstraint (view ty a' `TEq` TyCon "Bool" `as` phantom KindType) IfCondition s
    require $ newConstraint (view ty b' `TEq` view ty c') IfCongruence s
    return (view ty b' :< If a' b' c')

  Lambda p e -> closure $ do
    op <- freshTyOpUni
    (p', e') <- bind op (p, e)
    return (fun (view ty p') (view ty e') :< Lambda p' e')

  Lit x -> do
    let t = case x of { Int _ -> TyCon "Int" ; Bool _ -> TyCon "Bool" ; String _ -> TyCon "String" ; Char _ -> TyCon "Char" }
    return (t `as` phantom KindType :< Lit x)

  Read n e -> do
    t <- read s n
    tEnv %= intro n (mono t)
    e' <- exp e
    tEnv %= elim
    return (view ty e' :< view value e')

  Record r -> do
    r' <- traverse exp r
    let t = TyRecord (fmap (view ty) r') `as` phantom KindType
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

equals :: [(Source, Annotated Type)] -> Reason -> Praxis (Annotated Type)
equals ((_, t):ts) r = sequence [equal t t' r s | (s, t') <- ts] >> return t

bind :: Annotated TyOp -> (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
bind op (p, e) = do
  (i, p') <- pat op p
  e' <- exp e
  tEnv %= elimN i
  return (over ty (\t -> TyOp op t `as` phantom KindType) p', e')

pat :: Annotated TyOp -> Annotated Pat -> Praxis (Int, Annotated Pat)
pat op = splitPair $ \s -> \case

  PatAt v p -> do
    (i, p') <- pat op p
    let t = view ty p'
    tEnv %= intro v (mono t)
    return (i + 1, t :< PatAt v p')

  PatHole -> do
    t <- freshTyUni
    return (0, t :< PatHole)

  PatLit l -> return (0, TyCon (lit l) `as` phantom KindType :< PatLit l)
    where lit (Bool _)   = "Bool"
          lit (Char _)   = "Char"
          lit (Int _)    = "Int"
          lit (String _) = "String"

  PatRecord r -> do
    (Sum i, r') <- traverse (over first Sum) <$> traverse (pat op) r
    let t = TyRecord (fmap (view ty) r') `as` phantom KindType
    return (i, t :< PatRecord r')

  PatVar v -> do
    t <- freshTyUni
    tEnv %= intro v (mono (TyOp op t `as` phantom KindType))
    return (1, t :< PatVar v)

  PatCon n ps -> do
    -- Lookup the data alternative with this name
    DataAltInfo ns ct args rt <- getData s n
    unless (length args == length ps) $ throwAt s $ "wrong number of arguments applied to data constructor " <> quote (pretty n)
    (Sum i, ps') <- traverse (over first Sum) <$> traverse (pat op) ps
    f <- ungeneralise ns
    let rt'   = f rt
        args' = map f args
    requires [ newConstraint (view ty p' `TEq` arg') (Custom "TODO: PatCon") s | (p', arg') <- zip ps' args' ]
    return (i, rt' :< PatCon n ps')
