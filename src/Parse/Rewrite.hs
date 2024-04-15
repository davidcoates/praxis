{-# LANGUAGE GADTs #-}

module Parse.Rewrite
  ( run
  ) where

import           Common
import           Introspect
import qualified Parse.Mixfix    as Mixfix
import           Praxis
import           Print
import           Stage
import           Term

import           Data.List       (intersect, intersperse, nub, partition, (\\))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ do
  stage .= Rewrite
  term <- rewriteTopLevel term
  display term `ifFlag` debug
  return term

-- Term rewriting. This is used to rewrite type-level variables to guarantee uniqueness which is needed for the solver.
-- The rewrite mapping is stored so it can be applied in reverse when displaying diagnostics to the user.

rewriteTopLevel :: Term a => Annotated a -> Praxis (Annotated a)
rewriteTopLevel term = case typeof (view value term) of
  IQType -> saveTyVarMap $ addRewriteFromQType term >> value (recurseTerm rewrite) term -- For testing
  _ -> rewrite term

rewrite :: Term a => Annotated a -> Praxis (Annotated a)
rewrite term = ($ term) $ case typeof (view value term) of
  IType   -> rewriteType
  IView   -> rewriteView
  ITyPat  -> rewriteTyPat
  IQTyVar -> rewriteQTyVar
  IExp    -> rewriteExp
  IDecl   -> rewriteDecl
  IPat    -> rewritePat
  _       -> value (recurseTerm rewrite)

saveVarMap :: Praxis a -> Praxis a
saveVarMap c = do
  m <- use (rewriteMap . varMap)
  v <- c
  rewriteMap . varMap .= m
  return v

saveTyVarMap :: Praxis a -> Praxis a
saveTyVarMap c = do
  m <- use (rewriteMap . tyVarMap)
  v <- c
  rewriteMap . tyVarMap .= m
  return v

isUnique :: Eq a => [a] -> Bool
isUnique xs = length (nub xs) == length xs

addVarRewrites :: Source -> [Name] -> Praxis ()
addVarRewrites src varNames = do
  when (not (isUnique varNames)) $ throwAt src "variables are not distinct"
  vars <- series $ [ (\m -> (n, m)) <$> freshVar n | n <- varNames ]
  rewriteMap . varMap %= (Map.fromList vars `Map.union`)

addTyVarRewrites :: Source -> [Name] -> Praxis ()
addTyVarRewrites src tyVarNames = do
  tyVars <- series $ [ (\m -> (n, m)) <$> freshTyVar n | n <- tyVarNames ]
  when (not (isUnique (map fst tyVars))) $ throwAt src "type variables are not distinct"
  rewriteMap . tyVarMap %= (Map.fromList tyVars `Map.union`)

addRewriteFromTyPat :: Annotated TyPat -> Praxis ()
addRewriteFromTyPat tyPat = do
  let tyVars = extract (embedMonoid f) tyPat
      f = \case
        TyPatVar n       -> [n]
        TyPatViewVar _ n -> [n]
        _                -> []
  addTyVarRewrites (view source tyPat) tyVars

addRewriteFromQType :: Annotated QType -> Praxis ()
addRewriteFromQType ((src, _) :< Forall vs _ _) = do
  let tyVars = [ n | QTyVar n <- map (view value) vs ] ++ [ n | QViewVar _ n <- map (view value) vs ]
  addTyVarRewrites src tyVars

addRewriteFromPat :: Annotated Pat -> Praxis ()
addRewriteFromPat pat = do
  let vars = extract (embedMonoid f) pat
      f = \case
        PatVar n  -> [n]
        PatAt n _ -> [n]
        _         -> []
  addVarRewrites (view source pat) vars

rewriteTyVar :: Name -> Praxis Name
rewriteTyVar n = do
  m <- use (rewriteMap . tyVarMap)
  return $ case Map.lookup n m of
    Nothing -> n
    Just n  -> n

rewriteVar :: Name -> Praxis Name
rewriteVar n = do
  m <- use (rewriteMap . varMap)
  return $ case Map.lookup n m of
    Nothing -> n
    Just n  -> n

rewriteType :: Annotated Type -> Praxis (Annotated Type)
rewriteType (a :< ty) = (a :<) <$> case ty of

  TyVar n -> TyVar <$> rewriteTyVar n

  _       -> recurseTerm rewrite ty


rewriteView  :: Annotated View -> Praxis (Annotated View)
rewriteView (a :< view) = (a :<) <$> case view of

  ViewVar d n -> ViewVar d <$> rewriteTyVar n

  _           -> recurseTerm rewrite view


rewriteTyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
rewriteTyPat (a :< tyPat) = (a :<) <$> case tyPat of

  TyPatVar n       -> TyPatVar <$> rewriteTyVar n

  TyPatViewVar d n -> TyPatViewVar d <$> rewriteTyVar n

  _                -> recurseTerm rewrite tyPat


rewriteQTyVar :: Annotated QTyVar -> Praxis (Annotated QTyVar)
rewriteQTyVar (a :< qTyVar) = (a :<) <$> case qTyVar of

  QTyVar n     -> QTyVar <$> rewriteTyVar n

  QViewVar d n -> QViewVar d <$> rewriteTyVar n


rewriteAlt :: (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
rewriteAlt (pat, exp) = saveVarMap $ do
  addRewriteFromPat pat
  pat <- rewritePat pat
  exp <- rewriteExp exp
  return (pat, exp)

rewriteBind :: Annotated Bind -> Praxis (Annotated Bind)
rewriteBind (a :< Bind pat exp) = do
  exp <- rewriteExp exp
  addRewriteFromPat pat
  pat <- rewritePat pat
  return (a :< Bind pat exp)

rewriteExp :: Annotated Exp -> Praxis (Annotated Exp)
rewriteExp (a :< exp) = (a :<) <$> case exp of

  Var name -> Var <$> rewriteVar name

  Read name exp -> Read <$> rewriteVar name <*> rewriteExp exp

  Where exp decls -> saveVarMap $ do
    decls <- traverse rewriteDecl decls
    exp <- rewriteExp exp
    return $ Where exp decls

  Case exp alts -> do
    exp <- rewriteExp exp
    alts <- traverse rewriteAlt alts
    return $ Case exp alts

  Cases alts -> do
    alts <- traverse rewriteAlt alts
    return $ Cases alts

  exp@(Lambda pat _) -> saveVarMap $ do
    addRewriteFromPat pat
    recurseTerm rewrite exp

  Let bind exp -> saveVarMap $ do
    bind <- rewriteBind bind
    exp <- rewriteExp exp
    return $ Let bind exp

  _ -> recurseTerm rewrite exp


rewritePat :: Annotated Pat -> Praxis (Annotated Pat)
rewritePat (a :< pat) = (a :<) <$> case pat of

  PatVar n  -> PatVar <$> rewriteVar n

  PatAt n p -> PatAt <$> rewriteVar n <*> rewritePat p

  _         -> recurseTerm rewrite pat


rewriteDecl :: Annotated Decl -> Praxis (Annotated Decl)
rewriteDecl ((src, a) :< decl) = ((src, a) :<) <$> case decl of

  DeclVar name sig exp -> do
    name' <- freshVar name
    let rewriteBody = (,) <$> traverse rewrite sig <*> rewriteExp exp
    (sig, exp) <- case sig of
      Nothing  -> rewriteBody
      Just sig -> saveTyVarMap (addRewriteFromQType sig >> rewriteBody)
    rewriteMap . varMap %= (Map.insert name name')
    return (DeclVar name' sig exp)

  DeclData name tyPat alts -> case tyPat of
    Nothing    -> recurseTerm rewrite decl
    Just tyPat -> saveTyVarMap (addRewriteFromTyPat tyPat >> recurseTerm rewrite decl)

  DeclEnum name alts -> return $ DeclEnum name alts

  DeclRec decls -> do
    addVarRewrites src (map (\(_ :< DeclVar name _ _) -> name) decls)
    decls <- traverse (value rewriteDeclVar) decls
    return (DeclRec decls)
    where
      rewriteDeclVar :: Decl -> Praxis Decl
      rewriteDeclVar decl@(DeclVar name sig exp) = case sig of
        Nothing  -> rewriteDeclVar' decl
        Just sig -> saveTyVarMap (addRewriteFromQType sig >> rewriteDeclVar' decl)
      rewriteDeclVar' :: Decl -> Praxis Decl
      rewriteDeclVar' (DeclVar name sig exp) = DeclVar <$> rewriteVar name <*> traverse rewrite sig <*> rewriteExp exp

  DeclOp op name opRules -> (\name -> DeclOp op name opRules) <$> rewriteVar name

