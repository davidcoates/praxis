{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}

module Check.Type.Generate
  ( run
  , recursive
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
import           Print
import           Stage
import           Term

import           Control.Monad      (replicateM)
import           Data.Foldable      (foldMap, foldlM)
import           Data.List          (nub, partition, sort)
import           Data.Maybe         (isJust, mapMaybe)
import           Data.Set           (Set)
import qualified Data.Set           as Set
import           Prelude            hiding (exp, log, lookup, read)
import qualified Prelude            (lookup)

ty :: (Term a, Functor f, Annotation a ~ Annotated Type) => (Annotated Type -> f (Annotated Type)) -> Annotated a -> f (Annotated a)
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
ungeneralise :: [QTyVar] -> Praxis (Annotated Type -> Annotated Type)
ungeneralise vs = do
  vars <- series $ [ (\t -> (n, view value t)) <$> freshTyUni | QTyVar n <- vs ]
  opVars <- series $ [ (\t -> (n, view value t)) <$> freshTyOpUni | QTyOpVar n <- vs ]
  return $ sub $ \x -> case typeof x of
    IType |   TyVar n <- x -> n `Prelude.lookup` vars
    ITyOp | TyOpVar n <- x -> n `Prelude.lookup` opVars
    _                      -> Nothing

ungeneraliseQType :: Annotated QType -> Praxis (Annotated Type)
ungeneraliseQType (_ :< Forall vs t) = ($ t) <$> ungeneralise vs

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
      return $ phantom (TyApply (phantom (TyOp (phantom TyOpBang))) t)
    Nothing -> throwAt s (NotInScope n)

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
mark :: Source -> Name -> Praxis (Annotated Type)
mark s n = do
  l <- use tEnv
  case LEnv.lookupFull n l of
    Just (c, u, t) -> do
      t <- ungeneraliseQType t
      tEnv %= LEnv.mark n
      requires [ newConstraint (Share t) (MultiUse n) s | u ]
      requires [ newConstraint (Share t) (Captured n) s | c ]
      return t
    Nothing -> throwAt s (NotInScope n)

getType :: Source -> Name -> Praxis (Annotated QType)
getType s n = do
  l <- use tEnv
  case lookup n l of
    Just t  -> return t
    Nothing -> throwAt s (NotInScope n)

getData :: Source -> Name -> Praxis DataAltInfo
getData s n = do
  l <- use daEnv
  case lookup n l of
    Just v  -> return (view (annotation . just) v)
    Nothing -> throwAt s $ "data constructor " <> quote (pretty n) <> " is not in scope"

run :: Term a => Annotated a -> Praxis (Annotated a)
run x = save stage $ do
  stage .= TypeCheck Generate
  x' <- generate x
  display x' `ifFlag` debug
  cs <- use (our . constraints)
  (`ifFlag` debug) $ do
    display (separate "\n\n" (nub . sort $ cs))
    use tEnv >>= display
    use daEnv >>= display
  return x'

generate :: forall a. Term a => Annotated a -> Praxis (Annotated a)
generate x = ($ x) $ case witness :: I a of
  IProgram -> program
  IExp     -> exp
  IBind    -> bind
  IDataAlt -> error "standalone DataAlt"
  IDecl    -> error "standalone Decl"
  IPat     -> error "standalone Pat"
  _        -> value (recurse generate)

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

equal :: Annotated Type -> Annotated Type -> Reason -> Source -> Praxis ()
equal t1 t2 r s = require $ newConstraint (t1 `TEq` t2) r s

-- TODO use introspection?
patToTy :: Annotated TyPat -> Annotated Type
patToTy = over value patToTy' where
  patToTy' = \case
    TyPatVar n    -> TyVar n
    TyPatPack a b -> TyPack (patToTy a) (patToTy b)

unis :: Annotated TyPat -> Set QTyVar
unis = extract (embedMonoid f) where
  f = \case
    TyPatVar n -> Set.singleton (QTyVar n)
    _          -> Set.empty

program :: Annotated Program -> Praxis (Annotated Program)
program (a :< Program ds) = do
  ds <- decls ds
  return (a :< Program ds)

dataAlt :: [QTyVar] -> Annotated Type -> Annotated DataAlt -> Praxis (Annotated DataAlt)
dataAlt vars rt ((s, Nothing) :< DataAlt n at) = do
  let ct = phantom $ Forall vars $ case at of -- Type of the constructor
        Just at -> fun at rt
        Nothing -> rt
      da = ((s, Just (DataAltInfo ct at rt)) :< DataAlt n at)
  daEnv %= Env.intro n da
  return da

recursive :: Annotated Exp -> Bool
recursive x = case view value x of
    Lambda _ _ -> True
    Cases _    -> True
    _          -> False

decls :: [Annotated Decl] -> Praxis [Annotated Decl]
decls ds = do
  ds' <- mapM preDeclare ds
  mapM (\(t, d) -> decl t d) ds'
  where
    declare n sig = do
      t <- case sig of Nothing -> mono <$> freshTyUni
                       Just t  -> pure t
      tEnv %= intro n t
      return t
    preDeclare d = case d of
      (_ :< DeclVar n sig e) | recursive e -> do { t <- declare n sig; return (Just t, d) }
      _                                    -> return (Nothing, d)

decl :: Maybe (Annotated QType) -> Annotated Decl -> Praxis (Annotated Decl)
decl forwardT = splitTrivial $ \s -> \case

  -- TODO Share constraints needed!
  DeclData n p alts -> do
    -- TODO could be kind annotated to avoid this lookup
    Just k <- kEnv `uses` Env.lookup n

    -- The return type of the constructors
    let rt = case p of
          Nothing                                -> TyCon n `as` k
          Just p | KindFun k1 k2 <- view value k -> TyApply (TyCon n `as` k) (patToTy p) `as` k2
        vars = Set.toList (foldMap unis p)

    alts' <- traverse (dataAlt vars rt) alts
    return $ DeclData n p alts'

  -- TODO check no duplicate variables
  DeclVar n sig e -> do
    e' <- exp e
    -- TODO this won't work for nested polymorphic definitions
    let t = view ty e'
    case forwardT of
      Just (_ :< Forall _ t') -> equal t' t (FuncSignature n) s
      Nothing                 -> tEnv %= intro n (mono t)
    case sig of
      Just (_ :< Forall _ t') -> equal t' t (FuncCongruence n) s
      Nothing                 -> return ()
    return $ DeclVar n Nothing e'

  op@(DeclOp _ _ _) -> return op

  DeclSyn s t -> return $ DeclSyn s t


mono :: Annotated Type -> Annotated QType
mono t = (view source t, Nothing) :< Forall [] t

exp :: Annotated Exp -> Praxis (Annotated Exp)
exp = split $ \s -> \case

  Apply f x -> do
    yt <- freshTyUni
    f' <- exp f
    x' <- exp x
    let ft = view ty f'
    let xt = view ty x'
    require $ newConstraint (ft `TEq` fun xt yt) FuncApplication s
    return (yt :< Apply f' x')

  Case x alts -> do
    x' <- exp x
    let xt = view ty x'
    op <- freshTyOpUni
    alts' <- parallel (map (alt op) alts)
    t1 <- equals (map fst alts') CaseCongruence
    t2 <- equals (map snd alts') CaseCongruence
    equal xt t1 CaseCongruence s -- TODO probably should pick a better name for this
    return (t2 :< Case x' alts')

  Cases alts -> closure $ do
    op <- freshTyOpUni
    alts' <- parallel (map (alt op) alts)
    t1 <- equals (map fst alts') CaseCongruence
    t2 <- equals (map snd alts') CaseCongruence
    return (fun t1 t2 :< Cases alts')

  Con n -> do
    DataAltInfo qt _ _ <- getData s n
    t <- ungeneraliseQType qt
    return (t :< Con n)

  Do ss -> save tEnv $ do
    ss' <- traverse generate ss
    case view value (last ss') of
      StmtExp ((_, Just t) :< _) -> return (t :< Do ss')
      _                          -> throwAt s $ ("do block must end in an expression" :: String)

  If a b c -> do
    a' <- exp a
    (b', c') <- join (exp b) (exp c)
    require $ newConstraint (view ty a' `TEq` TyCon "Bool" `as` phantom KindType) IfCondition s
    require $ newConstraint (view ty b' `TEq` view ty c') IfCongruence s
    return (view ty b' :< If a' b' c')

  Lambda p e -> closure $ do
    op <- freshTyOpUni
    (p', e') <- alt op (p, e)
    return (fun (view ty p') (view ty e') :< Lambda p' e')

  Let b x -> save tEnv $ do
    b' <- bind b
    x' <- exp x
    return (view ty x' :< Let b' x')

  -- TODO pull from environment?
  Lit x -> ((\t -> t `as` phantom KindType :< Lit x) <$>) $ case x of
    Int  _   -> return $ TyCon "Int"
    Bool _   -> return $ TyCon "Bool"
    Char _   -> return $ TyCon "Char"
    String _ -> do
      o <- freshTyOpUni
      let ot = TyOp o `as` phantom KindOp
          a = TyCon "Array" `as` phantom (KindFun (phantom KindType) (phantom KindType))
          ac = TyApply a (TyCon "Char" `as` phantom KindType) `as` phantom KindType
      return $ TyApply ot ac

  Read n e -> do
    t <- read s n
    tEnv %= intro n (mono t)
    e' <- exp e
    tEnv %= elim
    return (view ty e' :< view value e')

  Pair p q -> do
    p' <- exp p
    q' <- exp q
    let t = TyPair (view ty p') (view ty q') `as` phantom KindType
    return (t :< Pair p' q')

{-
  Sig e t -> do
    e' <- exp e
    t <- impure t
    equalI t (ty e') (UserSignature Nothing) s
    return e'
-}

  Switch alts -> do
    cs <- sequence (map (exp . fst) alts)
    requires [ newConstraint (view ty c `TEq` TyCon "Bool" `as` phantom KindType) SwitchCondition (view source c) | c <- cs]
    es <- parallel (map (exp . snd) alts)
    t <- equals es SwitchCongruence
    return (t :< Switch (zip cs es))

  Unit -> do
    let t = TyUnit `as` phantom KindType
    return (t :< Unit)

  Var n -> do
    t <- mark s n
    return (t :< Var n)

  Where x bs -> save tEnv $ do
    bs' <- decls bs
    x' <- exp x
    return (view ty x' :< Where x' bs')


equals :: (Term a, Annotation a ~ Annotated Type) => [Annotated a] -> Reason -> Praxis (Annotated Type)
equals es = equals' (map (\e -> (view source e, view ty e)) es) where
  equals' :: [(Source, Annotated Type)] -> Reason -> Praxis (Annotated Type)
  equals' ((_, t):ts) r = sequence [equal t t' r s | (s, t') <- ts] >> return t


bind :: Annotated Bind -> Praxis (Annotated Bind)
bind = splitTrivial $ \s -> \case

  Bind p e -> do
    e' <- exp e
    op <- freshTyOpUni
    p' <- pat op p
    equal (view ty p') (view ty e') (BindCongruence) (view source p <> view source e)
    return $ Bind p' e'


alt :: Annotated TyOp -> (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
alt op (p, e) = save tEnv $ do
  p' <- pat op p
  e' <- exp e
  return (p', e')


pat :: Annotated TyOp -> Annotated Pat -> Praxis (Annotated Pat)
pat op p = snd <$> pat' p where

  wrap t = TyApply (TyOp op `as` phantom KindOp) t `as` phantom KindType

  pat' :: Annotated Pat -> Praxis (Annotated Type, Annotated Pat)
  pat' = splitPair $ \s -> \case

    PatAt v p -> do
      (t, p') <- pat' p
      tEnv %= intro v (mono t)
      require $ newConstraint (Share t) (MultiAlias v) s
      return (t, wrap t :< PatAt v p')

    PatCon n p -> do
      -- Lookup the data alternative with this name
      DataAltInfo qt at rt <- getData s n
      when (isJust at /= isJust p) $ throwAt s $ "wrong number of arguments applied to data constructor " <> quote (pretty n)

      let Forall vs _ = view value qt
      f <- ungeneralise vs
      let rt' = f rt

      case p of
        Nothing -> return (rt', wrap rt' :< PatCon n Nothing)
        Just p -> do
          (pt, p') <- pat' p
          let Just at' = at
          require $ newConstraint (pt `TEq` f at') (ConPattern n) s
          return (rt', wrap rt' :< PatCon n (Just p'))

    PatHole -> do
      t <- freshTyUni
      return (t, wrap t :< PatHole)

    -- TODO think about how view literals would work, e.g. x@"abc"
    PatLit l -> let t = TyCon (lit l) `as` phantom KindType in return (t, t :< PatLit l) where
      lit = \case
        Bool _   -> "Bool"
        Char _   -> "Char"
        Int _    -> "Int"
        String _ -> "String"

    PatPair p q -> do
      (pt, p') <- pat' p
      (qt, q') <- pat' q
      let t = TyPair pt qt `as` phantom KindType
      return (t, wrap t :< PatPair p' q')

    PatUnit -> do
      let t = TyUnit `as` phantom KindType
      return (t, t :< PatUnit)

    PatVar v -> do
      t <- freshTyUni
      tEnv %= intro v (mono (wrap t))
      return (t, wrap t :< PatVar v)
