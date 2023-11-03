{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}

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

rewriteTopLevel :: forall a. Term a => Annotated a -> Praxis (Annotated a)
rewriteTopLevel term = case witness :: I a of
  IQType -> saveTyVarMap $ addRewriteFromQType term >> value (recurse rewrite) term -- For testing
  _ -> rewrite term

rewrite :: forall a. Term a => Annotated a -> Praxis (Annotated a)
rewrite term = ($ term) $ case witness :: I a of
  IProgram -> rewriteProgram
  IType    -> rewriteType
  IView    -> rewriteView
  ITyPat   -> rewriteTyPat
  IQTyVar  -> rewriteQTyVar
  IExp     -> rewriteExp
  IDecl    -> rewriteDecl
  IPat     -> rewritePat
  _        -> value (recurse rewrite)


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

mkVarRewriteMap :: Source -> [Name] -> Praxis (Map Name Name)
mkVarRewriteMap src varNames = do
  when (not (isUnique varNames)) $ throwAt src $ ("variables are not distinct" :: String)
  vars <- series $ [ (\m -> (n, m)) <$> freshVar n | n <- varNames ]
  return (Map.fromList vars)

mkTyRewriteMap :: Source -> [Name] -> Praxis (Map Name Name)
mkTyRewriteMap src tyVarNames = do
  tyVars <- series $ [ (\m -> (n, m)) <$> freshTyVar n | n <- tyVarNames ]
  when (not (isUnique (map fst tyVars))) $ throwAt src $ ("type variables are not distinct" :: String)
  return (Map.fromList tyVars)

addRewriteFromTyPat :: Annotated TyPat -> Praxis ()
addRewriteFromTyPat tyPat = do
  let tyVars = extract (embedMonoid f) tyPat
      f = \case
        TyPatVar n       -> [n]
        TyPatViewVar _ n -> [n]
        _                -> []
  m' <- mkTyRewriteMap (view source tyPat) tyVars
  m <- use (rewriteMap . tyVarMap)
  rewriteMap . tyVarMap .= (m' `Map.union` m)

addRewriteFromQType :: Annotated QType -> Praxis ()
addRewriteFromQType ((src, _) :< Forall vs _ _) = do
  let tyVars = [ n | QTyVar n <- map (view value) vs ] ++ [ n | QViewVar _ n <- map (view value) vs ]
  m' <- mkTyRewriteMap src tyVars
  m <- use (rewriteMap . tyVarMap)
  rewriteMap . tyVarMap .= (m' `Map.union` m)

addRewriteFromPat :: Annotated Pat -> Praxis ()
addRewriteFromPat pat = do
  let vars = extract (embedMonoid f) pat
      f = \case
        PatVar n  -> [n]
        PatAt n _ -> [n]
        _         -> []
  m' <- mkVarRewriteMap (view source pat) vars
  m <- use (rewriteMap . varMap)
  rewriteMap . varMap .= (m' `Map.union` m)

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
rewriteType = splitTrivial $ \src -> \case

  TyVar n -> TyVar <$> rewriteTyVar n

  ty      -> recurse rewrite ty


rewriteView  :: Annotated View -> Praxis (Annotated View)
rewriteView = splitTrivial $ \src -> \case

  ViewVar d n -> ViewVar d <$> rewriteTyVar n

  view'       -> recurse rewrite view'


rewriteTyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
rewriteTyPat = splitTrivial $ \src -> \case

  TyPatVar n -> TyPatVar <$> rewriteTyVar n

  TyPatViewVar d n -> TyPatViewVar d <$> rewriteTyVar n

  tyPat -> recurse rewrite tyPat


rewriteQTyVar :: Annotated QTyVar -> Praxis (Annotated QTyVar)
rewriteQTyVar = splitTrivial $ \src -> \case

  QTyVar n -> QTyVar <$> rewriteTyVar n

  QViewVar d n -> QViewVar d <$> rewriteTyVar n

rewriteAlt :: (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
rewriteAlt (pat, exp) = saveVarMap $ do
  addRewriteFromPat pat
  pat <- rewritePat pat
  exp <- rewriteExp exp
  return (pat, exp)

rewriteBind :: Annotated Bind -> Praxis (Annotated Bind)
rewriteBind (ann :< Bind pat exp) = do
  exp <- rewriteExp exp
  addRewriteFromPat pat
  pat <- rewritePat pat
  return (ann :< Bind pat exp)


rewriteStmts :: [Annotated Stmt] -> Praxis [Annotated Stmt]
rewriteStmts = \case

    [] -> return []

    ((ann :< StmtBind bind):stmts) -> saveVarMap $ do
        bind <- rewriteBind bind
        stmts <- rewriteStmts stmts
        return $ (ann :< StmtBind bind):stmts

    ((ann :< StmtExp exp):stmts) -> do
        exp <- rewriteExp exp
        stmts <- rewriteStmts stmts
        return $ (ann :< StmtExp exp):stmts


rewriteExp :: Annotated Exp -> Praxis (Annotated Exp)
rewriteExp = splitTrivial $ \src -> \case

  Var name -> Var <$> rewriteVar name

  Read name exp -> Read <$> rewriteVar name <*> rewriteExp exp

  Where exp decls -> saveVarMap $ do
    decls <- rewriteDecls decls
    exp <- rewriteExp exp
    return $ Where exp decls

  Do stmts -> Do <$> rewriteStmts stmts

  Case exp alts -> do
    exp <- rewriteExp exp
    alts <- traverse rewriteAlt alts
    return $ Case exp alts

  Cases alts -> do
    alts <- traverse rewriteAlt alts
    return $ Cases alts

  exp@(Lambda pat _) -> saveVarMap $ do
    addRewriteFromPat pat
    recurse rewrite exp

  Let bind exp -> saveVarMap $ do
    bind <- rewriteBind bind
    exp <- rewriteExp exp
    return $ Let bind exp

  exp -> recurse rewrite exp


rewriteDecl :: Annotated Decl -> Praxis (Annotated Decl)
rewriteDecl = splitTrivial $ \src -> \case

  DeclTerm name sig exp -> DeclTerm <$> rewriteVar name <*> traverse rewrite sig <*> rewriteExp exp

  decl -> recurse rewrite decl


rewritePat :: Annotated Pat -> Praxis (Annotated Pat)
rewritePat = splitTrivial $ \src -> \case

  PatVar n -> PatVar <$> rewriteVar n

  PatAt n p -> PatAt <$> rewriteVar n <*> rewritePat p

  pat -> recurse rewrite pat


rewriteProgram :: Annotated Program -> Praxis (Annotated Program)
rewriteProgram (ann :< Program decls) = do
  decls <- rewriteDecls' decls -- Note: Top level terms don't need to be rewritten
  return (ann :< Program decls)

declTermNames :: Annotated Decl -> [Name]
declTermNames decl = case view value decl of

  DeclTerm name _ _ -> [name]

  DeclRec decls     -> concatMap declTermNames decls

  _                 -> []


rewriteDecls :: [Annotated Decl] -> Praxis [Annotated Decl]
rewriteDecls decls = do
  let names = concatMap declTermNames decls
  m' <- mkVarRewriteMap (view source (head decls)) names
  m <- use (rewriteMap . varMap)
  rewriteMap . varMap .= (m' `Map.union` m)
  decls <- rewriteDecls' decls
  return decls

rewriteDecls' :: [Annotated Decl] -> Praxis [Annotated Decl]
rewriteDecls' []             = pure []
rewriteDecls' (decl : decls) = case view value decl of

  DeclTerm name sig exp -> do
    decl <- case sig of
      Nothing  -> rewriteDecl decl
      Just sig -> saveTyVarMap (addRewriteFromQType sig >> rewriteDecl decl)
    decls <- rewriteDecls' decls
    return (decl : decls)

  DeclData name tyPat alts -> do
    decl <- case tyPat of
      Nothing    -> rewriteDecl decl
      Just tyPat -> saveTyVarMap (addRewriteFromTyPat tyPat >> rewriteDecl decl)
    decls <- rewriteDecls' decls
    return (decl : decls)

  DeclRec recDecls -> do
    recDecls <- rewriteDecls' recDecls
    let decl' = (view tag decl) :< DeclRec recDecls
    decls <- rewriteDecls' decls
    return (decl' : decls)

  _ -> do
    decl <- rewriteDecl decl
    decls <- rewriteDecls' decls
    return (decl : decls)
