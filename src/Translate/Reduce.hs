{-# LANGUAGE GADTs #-}

module Translate.Reduce
  ( run
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term
import           Translate.State

import           Data.Foldable   (toList)
import           Data.List       (nub)
import qualified Data.Map.Strict as Map
import           Data.Maybe      (fromJust)
import           Data.Sequence   ((|>))
import qualified Data.Sequence   as Seq
import qualified Data.Set        as Set


{-|
  Reduction converts terms to a "reduced" intermediate representation:
  - All polymorphic terms and types are specialised, so that the reduced tree is completely monomorphic with no type variables.
  - All function definitions (Lambda & Cases) are replaced by top-level defintions (DeclTermFn)

  The following constructs are eliminated:
  - Cases
  - Lambda
  - CaptureDetail
  - SpecialiseDetail
  - DeclTermRec
  And the following are introduced:
  - DeclTermFn
  - ApplyFnCore
  - ClosureCore
-}

{-
  { _capturesByName  :: Map Name Captures
  , _monoDeclsSeq    :: Seq (Annotated Decl)
  , _monoDeclsSet    :: Set Name
  , _polyDeclsByName :: Map Name (Annotated Decl)
  }

-}

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- reduce term
  display term `ifFlag` debug
  return term

reduce :: Term a => Annotated a -> Praxis (Annotated a)
reduce term = ($ term) $ case typeof (view value term) of
  IDecl     -> error "standalone Decl"
  IDeclTerm -> error "standalone DeclTerm"
  IDeclType -> error "standalone DeclType"
  IExp      -> reduceExp
  IProgram  -> reduceProgram
  IType     -> reduceType
  _         -> value (recurseTerm reduce)


-- FIXME
-- FIXME needs to include captures also
specialisedName :: Name -> [Annotated Type] -> Name
specialisedName name ts = name

unpackTyPat :: Annotated TyPat -> [Annotated TyPat]
unpackTyPat tyPat = case view value tyPat of
  TyPatPack t1 t2           -> unpackTyPat t1 ++ unpackTyPat t2
  TyPatVar _                -> [tyPat]
  TyPatViewVar RefOrValue _ -> [tyPat]
  TyPatViewVar Ref        _ -> []

unpackMaybeTyPat :: Maybe (Annotated TyPat) -> [Annotated TyPat]
unpackMaybeTyPat tyPat = case tyPat of
  Just tyPat -> unpackTyPat tyPat
  Nothing    -> []

reduceDeclType :: Annotated DeclType -> Praxis (Maybe (Annotated DeclType))
reduceDeclType decl = case view value decl of

  DeclTypeData _ name tyPat _ -> do
    let tyPats = unpackMaybeTyPat tyPat
    case tyPats of
      [] -> return (Just decl)
      _  -> do
        translateState . polyDeclsByName %= Map.insert name (phantom (DeclType decl))
        return Nothing

  DeclTypeEnum _ _ -> return (Just decl)


resolveCapture :: (Name, Annotated QType) -> Praxis [(Name, Annotated Type)]
resolveCapture (n, qTy) = do
  entry <- (translateState . capturesByName) `uses` Map.lookup n
  case entry of
    Just captures -> return captures
    Nothing -> case view value qTy of
      Mono t -> return [(n, t)]
      _      -> return [] -- inbuilts... what else?

resolveCaptures :: [(Name, Annotated QType)] -> Praxis [(Name, Annotated Type)]
resolveCaptures captures = (nub . concat) <$> mapM resolveCapture captures

reduceDeclTerm :: Annotated DeclTerm -> Praxis (Maybe (Annotated DeclTerm))
reduceDeclTerm decl = case view value decl of

  DeclTermRec decls -> do
    let (names, captures) = unzip $ map (\(_ :< DeclTermVar name _ (_ :< CaptureDetail captures _)) -> (name, captures)) decls
    captures <- resolveCaptures . filter (\(n, t) -> not (n `elem` names)) . nub . concat $ captures
    mapM_ (\name -> translateState . capturesByName %= Map.insert name captures) names
    mapM_ (reduceDeclTermFn captures) decls
    return Nothing

  DeclTermVar name sig (_ :< CaptureDetail captures fn) -> do
    captures <- resolveCaptures captures
    translateState . capturesByName %= Map.insert name captures
    reduceDeclTermFn captures decl
    return Nothing

  DeclTermVar _ _ _ -> do
    decl <- recurse reduce decl
    return (Just decl)


reduceDeclTermFn :: Captures -> Annotated DeclTerm -> Praxis ()
reduceDeclTermFn captures decl = case view value decl of

  DeclTermVar name (Just (_ :< Forall _ _ _)) _ -> do
    translateState . polyDeclsByName %= Map.insert name (phantom (DeclTerm decl))

  DeclTermVar name _ (_ :< CaptureDetail _ fn) -> do
    arg <- freshVar "_arg"
    fn <- reduceExp fn
    let
      Just (_ :< TyFn t1 t2) = view annotation fn
      exp = case view value fn of
        Lambda pat exp -> Let (phantom (Bind pat (Var arg `as` t1))) exp `as` t2
        Cases cs       -> Case (Var arg `as` t1) cs `as` t2
    let decl = phantom (DeclTerm (phantom (DeclTermFn name captures (arg, t1) exp)))
    translateState . monoDeclsSeq %= (|> decl)
    translateState . monoDeclsSet %= Set.insert name


reduceDecl :: Annotated Decl -> Praxis [Annotated Decl]
reduceDecl decl = do
  decl <- reduceDecl' decl
  decls <- use (translateState . monoDeclsSeq)
  return $ toList decls ++ toList decl

reduceDecl' :: Annotated Decl -> Praxis (Maybe (Annotated Decl))
reduceDecl' (a :< decl) = case decl of

  DeclTerm decl -> do
    decl <- reduceDeclTerm decl
    case decl of
      Nothing   -> return Nothing
      Just decl -> return $ Just (a :< DeclTerm decl)

  DeclType decl -> do
    decl <- reduceDeclType decl
    case decl of
      Nothing   -> return Nothing
      Just decl -> return $ Just (a :< DeclType decl)


reduceType :: Annotated Type -> Praxis (Annotated Type)
reduceType ty = return ty -- TODO

reduceProgram :: Annotated Program -> Praxis (Annotated Program)
reduceProgram (a :< Program decls) = do
  decls <- concat <$> mapM reduceDecl decls
  return (a :< Program decls)

reduceExp :: Annotated Exp -> Praxis (Annotated Exp)
reduceExp (a :< exp) = case exp of

  Where exp decls -> do
    decls <- concat . (map toList) <$> mapM reduceDeclTerm decls
    exp <- reduceExp exp
    return (a :< Where exp decls)

  -- TODO specialise, lambda, etc

  _ -> recurse reduce (a :< exp) -- TODO
