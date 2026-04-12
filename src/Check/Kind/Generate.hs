module Check.Kind.Generate
  ( run
  ) where

import           Check.Kind.State
import           Check.State
import           Common
import           Inbuilts
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Monad.Trans (lift)
import           Data.List           (nub, sort)
import qualified Data.Map.Strict     as Map
import qualified Data.Set            as Set


run :: IsTerm a => Annotated Parse a -> KindM (Annotated KindCheck a)
run term = do
  term <- generate term
  lift $ display KindCheck "annotated term" term `ifFlag` debug
  requirements' <- use (kindSolveLocal . requirements)
  lift $ display KindCheck "requirements" (separate "\n" (nub . sort $ Set.toList requirements')) `ifFlag` debug
  return term

generate :: IsTerm a => Annotated Parse a -> KindM (Annotated KindCheck a)
generate term = ($ term) $ case typeof (view value term) of
  BindT           -> auto
  DataConT        -> generateDataCon
  DeclT           -> generateDecl
  DeclTermT       -> generateDeclTerm
  DeclTypeT       -> generateDeclType
  ExpT            -> auto
  PatT            -> auto
  ProgramT        -> auto
  QTypeT          -> generateQType
  TypeT           -> generateType
  TypeConstraintT -> auto
  TypePatT        -> generateTypePat
  ty              -> error (show ty)
  where
    auto :: (IsTerm a, Annotation Parse a ~ Annotation KindCheck a) => Annotated Parse a -> KindM (Annotated KindCheck a)
    auto = value (recurseTerm generate)

introCon :: Source -> Name -> Annotated KindCheck Kind -> KindM ()
introCon src name kind = do
  entry <- lift $ (checkState . kindState . typeConEnv) `uses` Map.lookup name
  case entry of
    Just _ -> lift $ throwAt KindCheck src $ "type " <> pretty name <> " redeclared"
    _      -> lift $ checkState . kindState . typeConEnv %= Map.insert name kind

introVar :: Source -> Flavor -> Name -> Annotated KindCheck Kind -> KindM Name
introVar src flavor name kind = do
  rename <- lift $ freshVar name
  typeVarRenameLocal %= Map.insert name rename
  Nothing <- typeVarEnvLocal `uses` Map.lookup rename -- sanity check
  typeVarEnvLocal %= Map.insert rename (flavor, kind)
  return rename

lookupCon :: Source -> Name -> KindM (Annotated KindCheck Kind)
lookupCon src name = do
  entry <- lift $ (checkState . kindState . typeConEnv) `uses` Map.lookup name
  case entry of
    Just kind -> return kind
    Nothing   -> lift $ throwAt KindCheck src $ "type " <> pretty name <> " is not in scope"

lookupVar :: Source -> Flavor -> Name -> KindM (Name, Annotated KindCheck Kind)
lookupVar src flavor name = do
  entry <- (typeVarRenameLocal) `uses` Map.lookup name
  let rename = case entry of { Just rename -> rename; Nothing -> name }
  entry <- typeVarEnvLocal `uses` Map.lookup rename
  case entry of
    Just (flavor', kind)
      | flavor == flavor' -> return (rename, kind)
      | otherwise         -> lift $ throwAt KindCheck src $ "type variable " <> pretty name <> " has the wrong flavor"
    Nothing -> lift $ throwAt KindCheck src $ "type variable " <> pretty name <> " is not in scope"

checkDistinct :: Source -> [Annotated s TypePat] -> KindM ()
checkDistinct src typePats = do
  let names = map (\(_ :< TypePatVar _ name) -> name) typePats
  unless (isDistinct names) $ lift $ throwAt KindCheck src ("type variables are not distinct" :: String)

scope :: KindM a -> KindM a
scope = save typeVarRenameLocal

require :: Annotated KindCheck (Requirement KindConstraint) -> KindM ()
require requirement = kindSolveLocal . requirements %= Set.insert requirement

generateType :: Annotated Parse Type -> KindM (Annotated KindCheck Type)
generateType (a@(src, _) :< ty) = (\(kind :< ty) -> ((src, kind) :< ty)) <$> case ty of

    TypeApply ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      argKind <- lift freshKindUni
      retKind <- lift freshKindUni
      require $ (src, KindReasonTypeApply ty1 ty2) :< Requirement (phantom (KindIsEq (view annotation ty1) (phantom (KindFn argKind retKind))))
      require $ (src, KindReasonTypeApply ty1 ty2) :< Requirement (phantom (KindIsSub (view annotation ty2) argKind))
      return (retKind :< TypeApply ty1 ty2)

    TypeApplyOp ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      require $ (src, KindReasonTypeApplyOp ty1 ty2) :< Requirement (phantom (KindIsEq (view annotation ty2) (phantom KindType)))
      return (phantom KindType :< TypeApplyOp ty1 ty2)

    TypeCon con -> do
      kind <- lookupCon src con
      return (kind :< TypeCon con)

    TypeFn ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      require $ (src, KindReasonType ty1) :< Requirement (phantom (KindIsEq (view annotation ty1) (phantom KindType)))
      require $ (src, KindReasonType ty2) :< Requirement (phantom (KindIsEq (view annotation ty2) (phantom KindType)))
      return (phantom KindType :< TypeFn ty1 ty2)

    TypeUnit -> do
      return (phantom KindType :< TypeUnit)

    TypeIdentityOp -> return (phantom KindView :< TypeIdentityOp)

    TypeSetOp tys -> do
      tys <- traverse generateType (Set.toList tys)
      let
        checkRefOrView :: Annotated KindCheck Type -> KindM ()
        checkRefOrView ty = case view value (view annotation ty) of
          KindRef  -> return ()
          KindView -> return ()
          _        -> lift $ throwAt KindCheck src $ "type " <> pretty ty <> " is in a type operator set but is not a type operator"
      traverse checkRefOrView tys
      let
        isRef = all (\op -> case view value (view annotation op) of { KindRef -> True; KindView -> False }) tys
      return (phantom (if isRef then KindRef else KindView) :< TypeSetOp (Set.fromList tys))

    TypePair ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      require $ (src, KindReasonType ty1) :< Requirement (phantom (KindIsEq (view annotation ty1) (phantom KindType)))
      require $ (src, KindReasonType ty2) :< Requirement (phantom (KindIsEq (view annotation ty2) (phantom KindType)))
      return (phantom KindType :< TypePair ty1 ty2)

    TypeVar flavor var -> do
      (var, kind) <- lookupVar src flavor var
      return (kind :< TypeVar flavor var)


-- TODO tidy this one up
generateTypePat :: Annotated Parse TypePat -> KindM (Annotated KindCheck TypePat)
generateTypePat typePat@((src, _) :< TypePatVar f var) = case f of

  Plain -> do
    kind <- lift freshKindUni
    var <- introVar src Plain var kind
    let typePat = (src, kind) :< TypePatVar f var
    require $ (src, KindReasonTypePat typePat) :< Requirement (phantom (KindIsPlain kind))
    return typePat

  Ref -> do
    let kind = phantom KindRef
    var <- introVar src Ref var kind
    let typePat = (src, kind) :< TypePatVar f var
    return typePat

  Value -> do
    kind <- lift freshKindUni
    var <- introVar src Value var kind
    let typePat = (src, kind) :< TypePatVar f var
    require $ (src, KindReasonTypePat typePat) :< Requirement (phantom (KindIsPlain kind))
    return typePat

  View -> do
    let kind = phantom KindView
    var <- introVar src View var kind
    let typePat = (src, kind) :< TypePatVar f var
    return typePat


generateDataCon :: Annotated Parse DataCon -> KindM (Annotated KindCheck DataCon)
generateDataCon (a@(src, _) :< DataCon name arg) = do
  arg <- generate arg
  let dataCon = (a :< DataCon name arg)
  require $ (src, KindReasonType arg) :< Requirement (phantom (KindIsEq (view annotation arg) (phantom KindType))) -- TODO should just match kind of data type?
  return dataCon


generateDecl :: Annotated Parse Decl -> KindM (Annotated KindCheck Decl)
generateDecl (a :< decl) = (a :<) <$> case decl of

  DeclRec decls -> do
    actions <- traverse preDeclare decls
    decls <- series actions
    return (DeclRec decls)
     where
      declTypeName (_ :< DeclTypeData _ name _ _) = name
      declTypeName (_ :< DeclTypeEnum name _)     = name
      preDeclare :: Annotated Parse DeclRec -> KindM (KindM (Annotated KindCheck DeclRec))
      preDeclare (a@(src, _) :< decl) = case decl of
        DeclRecTerm declTerm -> return $ (\declTerm -> a :< DeclRecTerm declTerm) <$> generateDeclTerm declTerm
        DeclRecType declType -> do { kind <- lift freshKindUni; introCon src (declTypeName declType) kind; return ((\declType -> a :< DeclRecType declType) <$> generateDeclType' (Just kind) declType) }

  _ -> recurseTerm generate decl


generateDeclType :: Annotated Parse DeclType -> KindM (Annotated KindCheck DeclType)
generateDeclType = generateDeclType' Nothing

generateDeclType' :: Maybe (Annotated KindCheck Kind) -> Annotated Parse DeclType -> KindM (Annotated KindCheck DeclType)
generateDeclType' forwardKind ((src, _) :< ty) = case ty of

  DeclTypeData mode name args alts -> do
    (args, alts) <- scope $ do
        checkDistinct src args
        args <- traverse generate args
        alts <- traverse generate alts
        return (args, alts)
    kind <- case forwardKind of
      Just kind -> return kind
      Nothing   -> do
        kind <- lift freshKindUni
        introCon src name kind
        return kind
    let
      mkKind :: [Annotated KindCheck TypePat] -> Annotated KindCheck Kind
      mkKind args = case args of
        []         -> phantom KindType
        (arg:args) -> phantom (KindFn (view annotation arg) (mkKind args))
    require $ (src, KindReasonData name args) :< Requirement (phantom (kind `KindIsEq` mkKind args))
    let
      deduce :: (Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint) -> [Annotated TypeCheck Type] -> (InstanceOrigin, Instance)
      -- FIXME: remove cast
      deduce mkConstraint args' = (Trivial, IsInstanceOnlyIf [ mkConstraint (sub (embedSub f) (cast conType)) | (_ :< DataCon _ conType) <- alts ]) where
        f (_ :< ty) = case ty of
          TypeVar _  n -> n `lookup` specializedVars
          _            -> Nothing
        specializedVars = zip (map (\(a :< TypePatVar _ n) -> n) args) args'
        cast :: forall a. IsTerm a => Annotated KindCheck a -> Annotated TypeCheck a
        cast ((src, _) :< term) = case termT :: TermT a of
          TypeT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

      instances = case mode of
        DataUnboxed -> Map.fromList
          [ (Clone,   deduce clone)
          , (Dispose, deduce dispose)
          , (Copy,    deduce copy)
          , (Capture, deduce capture)
          ]
        DataBoxed -> Map.fromList
          [ (Clone,   deduce clone)
          , (Dispose, deduce dispose)
          ]

    lift $ checkState . instanceEnv %= Map.insert name instances
    return $ (src, kind) :< DeclTypeData mode name args alts

  DeclTypeEnum name alts -> do
    let kind = phantom KindType
    introCon src name kind
    let
      instances = Map.fromList
        [ (Clone,   \_ -> (Trivial, IsInstance))
        , (Dispose, \_ -> (Trivial, IsInstance))
        , (Copy,    \_ -> (Trivial, IsInstance))
        , (Capture, \_ -> (Trivial, IsInstance))
        ]
    lift $ checkState . instanceEnv %= Map.insert name instances
    return $ (src, kind) :< DeclTypeEnum name alts


generateDeclTerm :: Annotated Parse DeclTerm -> KindM (Annotated KindCheck DeclTerm)
generateDeclTerm (a@(src, _) :< decl) = ((src, ()) :<) <$> case decl of

  DeclTermVar name (Just sig@((src, _) :< qTy@(Poly vs _ _))) exp -> scope $ do
    checkDistinct src vs
    sig <- ((src, ()) :<) <$> recurseTerm generate qTy
    exp <- generate exp
    return $ DeclTermVar name (Just sig) exp

  _ -> recurseTerm generate decl


generateQType :: Annotated Parse QType -> KindM (Annotated KindCheck QType)
generateQType (a@(src, _) :< qTy) = ((src, ()) :<) <$> case qTy of

  Poly vs _ _ -> checkDistinct src vs >> (scope $ recurseTerm generate qTy)

  _           -> recurseTerm generate qTy
