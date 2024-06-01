{-# LANGUAGE GADTs #-}

module Core.Lift
  ( run
  ) where

import           Common          hiding (lift)
import           Core.State
import           Introspect
import           Praxis
import           Stage
import           Term

import           Data.Foldable   (toList)
import           Data.List       (nub)
import qualified Data.Map.Strict as Map


{-|
  All function definitions (Lambda & Cases) are replaced by top-level defintions (DeclTermFnCore)

  The following constructs are eliminated:
  - Cases
  - Lambda
  - CaptureDetail
  - DeclTermRec
  And the following are introduced:
  - DeclTermFnCore
  - ClosureCore
-}

{-
-- _capturesByName  :: Map Name Captures

-}

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- lift term
  display "lifted term" term `ifFlag` debug
  return term

lift :: Term a => Annotated a -> Praxis (Annotated a)
lift term = ($ term) $ case typeof (view value term) of
  IDecl     -> error "standalone Decl"
  IDeclTerm -> error "standalone DeclTerm"
  IExp      -> liftExp
  IProgram  -> liftProgram
  _         -> value (recurseTerm lift)


resolveCapture :: (Name, Annotated QType) -> Praxis [(Name, Annotated Type)]
resolveCapture (n, qTy) = do
  entry <- (coreState . capturesByName) `uses` Map.lookup n
  case entry of
    Just captures -> return captures
    Nothing -> case view value qTy of
      Mono t -> return [(n, t)]
      _      -> return [] -- inbuilts... what else?

resolveCaptures :: [(Name, Annotated QType)] -> Praxis [(Name, Annotated Type)]
resolveCaptures captures = (nub . concat) <$> mapM resolveCapture captures

liftDeclTerm :: Annotated DeclTerm -> Praxis (Maybe (Annotated DeclTerm))
liftDeclTerm decl = case view value decl of

  DeclTermRec decls -> do
    let (names, captures) = unzip $ map (\(_ :< DeclTermVar name _ (_ :< CaptureDetail captures _)) -> (name, captures)) decls
    captures <- resolveCaptures . filter (\(n, t) -> not (n `elem` names)) . nub . concat $ captures
    mapM_ (\name -> coreState . capturesByName %= Map.insert name captures) names
    mapM_ (liftDeclTermFn captures) decls
    return Nothing

  DeclTermVar name sig (_ :< CaptureDetail captures fn) -> do
    captures <- resolveCaptures captures
    coreState . capturesByName %= Map.insert name captures
    liftDeclTermFn captures decl
    return Nothing

  DeclTermVar _ _ _ -> do
    decl <- recurse lift decl
    return (Just decl)


liftDeclTermFn :: Captures -> Annotated DeclTerm -> Praxis ()
liftDeclTermFn captures decl = case view value decl of

  DeclTermVar name _ (_ :< CaptureDetail _ fn) -> do
    liftFunction name captures fn


liftFunction :: Name -> Captures -> Annotated Exp -> Praxis ()
liftFunction name captures fn = do
  arg <- freshVar "_arg"
  fn <- liftExp fn
  let
    Just (_ :< TypeFn t1 t2) = view annotation fn
    exp = case view value fn of
      Lambda pat exp -> Let (phantom (Bind pat (Var arg `as` t1))) exp `as` t2
      Cases cs       -> Case (Var arg `as` t1) cs `as` t2
  let decl = phantom (DeclTermFnCore name captures (arg, t1) exp)
  coreState . liftedFunctions %= (decl:)

liftDecl :: Annotated Decl -> Praxis [Annotated Decl]
liftDecl decl = do
  decl <- liftDecl' decl
  decls <- use (coreState . liftedFunctions)
  coreState . liftedFunctions .= []
  return $ map (\decl -> phantom (DeclTerm decl)) decls ++ toList decl

liftDecl' :: Annotated Decl -> Praxis (Maybe (Annotated Decl))
liftDecl' (a :< decl) = case decl of

  DeclTerm decl -> do
    decl <- liftDeclTerm decl
    case decl of
      Nothing   -> return Nothing
      Just decl -> return $ Just (a :< DeclTerm decl)

  _ -> do
    decl <- recurse lift (a :< decl)
    return (Just decl)


liftProgram :: Annotated Program -> Praxis (Annotated Program)
liftProgram (a :< Program decls) = do
  decls <- concat <$> mapM liftDecl decls
  return (a :< Program decls)

liftExp :: Annotated Exp -> Praxis (Annotated Exp)
liftExp (a :< exp) = case exp of

  CaptureDetail captures fn -> do
    name <- freshVar "_anon"
    captures <- resolveCaptures captures
    liftFunction name captures fn
    return (a :< ClosureCore captures name)

  Where exp decls -> do
    decls <- concat . (map toList) <$> mapM liftDeclTerm decls
    exp <- liftExp exp
    return $ case decls of
      [] -> exp
      _  -> (a :< Where exp decls)

  _ -> recurse lift (a :< exp)
