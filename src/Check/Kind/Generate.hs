{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Check.Kind.Generate
  ( run
  ) where

import           Check.State
import           Common
import qualified Env.Strict      as Env
import           Inbuilts
import           Introspect
import           Praxis
import           Print
import           Term

import           Data.List       (nub, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set


require :: Tag (Source, KindReason) KindConstraint -> Praxis ()
require ((src, reason) :< con) = kindCheckState . requirements %= Set.insert ((src, Just reason) :< Requirement con)

getKind :: (Term a, Annotation a ~ Annotated Kind) => Annotated a -> Annotated Kind
getKind term = view (annotation . just) term

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- generate term
  display term `ifFlag` debug
  requirements' <- use (kindCheckState . requirements)
  display (separate "\n\n" (nub . sort $ Set.toList requirements')) `ifFlag` debug
  return term

-- TODO since we ignore annotation of input, could adjust this...
generate :: Term a => Annotated a -> Praxis (Annotated a)
generate term = ($ term) $ case typeof (view value term) of
  IDecl    -> generateDecl
  IType    -> generateType
  ITypeVar -> generateTypeVar
  IDataCon -> generateDataCon
  _        -> value (recurseTerm generate)

introKind :: Source -> Name -> Annotated Kind -> Praxis ()
introKind src name kind = do
  entry <- kEnv `uses` Env.lookup name
  case entry of
    Just _ -> throwAt src $ "type " <> quote (pretty name) <> " redeclared"
    _      -> kEnv %= Env.insert name kind


generateType :: Annotated Type -> Praxis (Annotated Type)
generateType (a@(src, _) :< ty) = (\(k :< t) -> ((src, Just k) :< t)) <$> case ty of

    TypeApply f x -> do
      f <- generateType f
      x <- generateType x
      k1 <- freshKindUni
      k2 <- freshKindUni
      require $ (src, KindReasonTypeApply f x) :< (getKind f `KindIsEq` phantom (KindFn k1 k2))
      require $ (src, KindReasonTypeApply f x) :< (getKind x `KindIsSub` k1)
      return (k2 :< TypeApply f x)

    TypeApplyOp f x -> do
      f <- generateType f
      x <- generateType x
      require $ (src, KindReasonTypeApplyOp f x) :< (getKind x `KindIsEq` phantom KindType)
      return (phantom KindType :< TypeApplyOp f x)

    TypeCon con -> do
      entry <- kEnv `uses` Env.lookup con
      case entry of
        Just k  -> return (k :< TypeCon con)
        Nothing -> throwAt src $ "type " <> quote (pretty con) <> " is not in scope"

    TypeFn t1 t2 -> do
      t1 <- generateType t1
      t2 <- generateType t2
      require $ (src, KindReasonType t1) :< (getKind t1 `KindIsEq` phantom KindType)
      require $ (src, KindReasonType t2) :< (getKind t2 `KindIsEq` phantom KindType)
      return (phantom KindType :< TypeFn t1 t2)

    TypeUnit -> do
      return (phantom KindType :< TypeUnit)

    TypeIdentityOp -> return (phantom KindView :< TypeIdentityOp)

    TypeSetOp tys -> do
      tys <- mapM generateType (Set.toList tys)
      let
        checkRefOrView :: Annotated Type -> Praxis ()
        checkRefOrView ty = case view value (getKind ty) of
          KindRef  -> return ()
          KindView -> return ()
          _        -> throwAt src $ "type " <> quote (pretty ty) <> " is in a type operator set but is not a type operator"
      mapM_ checkRefOrView tys
      let
        isRef = all (\op -> case view value (getKind op) of { KindRef -> True; KindView -> False }) tys
      return (phantom (if isRef then KindRef else KindView) :< TypeSetOp (Set.fromList tys))

    TypePair t1 t2 -> do
      t1 <- generateType t1
      t2 <- generateType t2
      require $ (src, KindReasonType t1) :< (getKind t1 `KindIsEq` phantom KindType)
      require $ (src, KindReasonType t2) :< (getKind t2 `KindIsEq` phantom KindType)
      return (phantom KindType :< TypePair t1 t2)

    TypeVar f var -> do
      Just k <- kEnv `uses` Env.lookup var
      return (k :< TypeVar f var)


generateTypeVar :: Annotated TypeVar -> Praxis (Annotated TypeVar)
generateTypeVar typeVar@(a@(src, _) :< TypeVarVar f var) = (\k -> (src, Just k) :< TypeVarVar f var) <$> case f of

  Plain -> do
    k <- freshKindUni
    introKind src var k
    require $ (src, KindReasonTypeVar typeVar) :< KindIsPlain k
    return k

  Ref -> do
    introKind src var (phantom KindRef)
    return (phantom KindRef)

  Value -> do
    k <- freshKindUni
    introKind src var k
    require $ (src, KindReasonTypeVar typeVar) :< KindIsPlain k
    return k

  View -> do
    introKind src var (phantom KindView)
    return (phantom KindView)


generateDataCon :: Annotated DataCon -> Praxis (Annotated DataCon)
generateDataCon (a@(src, _) :< DataCon name arg) = do
  arg <- generate arg
  let dataCon = (a :< DataCon name arg)
  require $ (src, KindReasonType arg) :< (getKind arg `KindIsEq` phantom KindType) -- TODO should just match kind of data type?
  return dataCon

generateDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
generateDeclType (a@(src, _) :< ty) = case ty of

  DeclTypeData mode name args alts -> do

    k <- freshKindUni
    when (mode == DataRec) $ introKind src name k
    (args, alts) <- save kEnv $ do
        args <- traverse generate args
        alts <- traverse generate alts
        return (args, alts)
    unless (mode == DataRec) $ introKind src name k
    let
      mkKind args = case args of
        []         -> phantom KindType
        (arg:args) -> phantom (KindFn (getKind arg) (mkKind args))
    require $ (src, KindReasonData name args) :< (k `KindIsEq` mkKind args)
    let
      deduce :: (Annotated Type -> TypeConstraint) -> [Annotated Type] -> (InstanceOrigin, Instance)
      deduce mkConstraint args' = (Trivial, IsInstanceOnlyIf [ mkConstraint (sub (embedSub f) conType) | (_ :< DataCon _ conType) <- alts ]) where
        f (_ :< t) = case t of
          TypeVar _  n -> n `lookup` specialisedVars
          _            -> Nothing
        specialisedVars = zip (map (\(a :< TypeVarVar f n) -> n) args) args'

      instances = case mode of
        DataUnboxed -> Map.fromList
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          , ("Copy",           deduce copy)
          , ("Capture",        deduce capture)
          ]
        _ -> Map.fromList
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          ]

    iEnv %= Env.insert name instances
    return $ (src, Just k) :< DeclTypeData mode name args alts

  DeclTypeEnum name alts -> do
    let k = phantom KindType
    introKind src name k
    let
      instances = Map.fromList
        [ ("Clone",   \_ -> (Trivial, IsInstance))
        , ("Dispose", \_ -> (Trivial, IsInstance))
        , ("Copy",    \_ -> (Trivial, IsInstance))
        , ("Capture", \_ -> (Trivial, IsInstance))
        ]
    iEnv %= Env.insert name instances
    return $ (src, Just k) :< DeclTypeEnum name alts


generateDecl :: Annotated Decl -> Praxis (Annotated Decl)
generateDecl (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclType ty -> DeclType <$> generateDeclType ty

  decl        -> recurseTerm generate decl
