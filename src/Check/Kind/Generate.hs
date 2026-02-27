module Check.Kind.Generate
  ( run
  ) where

import           Check.State
import           Common
import           Inbuilts
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Data.List       (nub, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set


run :: IsTerm a => Annotated Parse a -> Praxis (Annotated KindCheck a)
run term = do
  term <- generate term
  display KindCheck "annotated term" term `ifFlag` debug
  requirements' <- use (checkState . kindState . kindSolve . requirements)
  display KindCheck "requirements" (separate "\n" (nub . sort $ Set.toList requirements')) `ifFlag` debug
  return term

generate :: IsTerm a => Annotated Parse a -> Praxis (Annotated KindCheck a)
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
    auto :: (IsTerm a, Annotation Parse a ~ Annotation KindCheck a) => Annotated Parse a -> Praxis (Annotated KindCheck a)
    auto = value (recurseTerm generate)

introCon :: Source -> Name -> Annotated KindCheck Kind -> Praxis ()
introCon src name kind = do
  entry <- (checkState . kindState . typeConEnv) `uses` Map.lookup name
  case entry of
    Just _ -> throwAt KindCheck src $ "type " <> pretty name <> " redeclared"
    _      -> checkState . kindState . typeConEnv %= Map.insert name kind

introVar :: Source -> Flavor -> Name -> Annotated KindCheck Kind -> Praxis Name
introVar src flavor name kind = do
  entry <- (checkState . kindState . typeVarRename . counts) `uses` Map.lookup name
  let count = case entry of { Just count -> count; Nothing -> 0 }
  let rename = name ++ "_" ++ show count
  checkState . kindState . typeVarRename . counts %= Map.insert name (count + 1)
  checkState . kindState . typeVarRename . renames %= Map.insert name rename
  Nothing <- (checkState . kindState . typeVarEnv) `uses` Map.lookup rename -- sanity check
  checkState . kindState . typeVarEnv %= Map.insert rename (flavor, kind)
  return rename

lookupCon :: Source -> Name -> Praxis (Annotated KindCheck Kind)
lookupCon src name = do
  entry <- (checkState . kindState . typeConEnv) `uses` Map.lookup name
  case entry of
    Just kind -> return kind
    Nothing   -> throwAt KindCheck src $ "type " <> pretty name <> " is not in scope"

lookupVar :: Source -> Flavor -> Name -> Praxis (Name, Annotated KindCheck Kind)
lookupVar src flavor name = do
  entry <- (checkState . kindState . typeVarRename . renames) `uses` Map.lookup name
  let rename = case entry of { Just rename -> rename; Nothing -> name }
  entry <- (checkState . kindState . typeVarEnv) `uses` Map.lookup rename
  case entry of
    Just (flavor', kind)
      | flavor == flavor' -> return (rename, kind)
      | otherwise         -> throwAt KindCheck src $ "type variable " <> pretty name <> " has the wrong flavor"
    Nothing -> throwAt KindCheck src $ "type variable " <> pretty name <> " is not in scope"

checkDistinct :: Source -> [Annotated s TypePat] -> Praxis ()
checkDistinct src typePats = do
  let names = map (\(_ :< TypePatVar _ name) -> name) typePats
  unless (isDistinct names) $ throwAt KindCheck src ("type variables are not distinct" :: String)

scope :: Praxis a -> Praxis a
scope block = save (checkState . kindState . typeVarRename . renames) $ block

require :: Annotated KindCheck (Requirement KindConstraint) -> Praxis ()
require requirement = checkState . kindState . kindSolve . requirements %= Set.insert requirement

generateType :: Annotated Parse Type -> Praxis (Annotated KindCheck Type)
generateType (a@(src, _) :< ty) = (\(kind :< ty) -> ((src, kind) :< ty)) <$> case ty of

    TypeApply ty1 ty2 -> do
      ty1 <- generateType ty1
      ty2 <- generateType ty2
      argKind <- freshKindUni
      retKind <- freshKindUni
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
        checkRefOrView :: Annotated KindCheck Type -> Praxis ()
        checkRefOrView ty = case view value (view annotation ty) of
          KindRef  -> return ()
          KindView -> return ()
          _        -> throwAt KindCheck src $ "type " <> pretty ty <> " is in a type operator set but is not a type operator"
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
generateTypePat :: Annotated Parse TypePat -> Praxis (Annotated KindCheck TypePat)
generateTypePat typePat@((src, _) :< TypePatVar f var) = case f of

  Plain -> do
    kind <- freshKindUni
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
    kind <- freshKindUni
    var <- introVar src Value var kind
    let typePat = (src, kind) :< TypePatVar f var
    require $ (src, KindReasonTypePat typePat) :< Requirement (phantom (KindIsPlain kind))
    return typePat

  View -> do
    let kind = phantom KindView
    var <- introVar src View var kind
    let typePat = (src, kind) :< TypePatVar f var
    return typePat


generateDataCon :: Annotated Parse DataCon -> Praxis (Annotated KindCheck DataCon)
generateDataCon (a@(src, _) :< DataCon name arg) = do
  arg <- generate arg
  let dataCon = (a :< DataCon name arg)
  require $ (src, KindReasonType arg) :< Requirement (phantom (KindIsEq (view annotation arg) (phantom KindType))) -- TODO should just match kind of data type?
  return dataCon


generateDecl :: Annotated Parse Decl -> Praxis (Annotated KindCheck Decl)
generateDecl (a :< decl) = (a :<) <$> case decl of

  DeclRec decls -> do
    actions <- traverse preDeclare decls
    decls <- series actions
    return (DeclRec decls)
     where
      declTypeName (_ :< DeclTypeData _ name _ _) = name
      declTypeName (_ :< DeclTypeEnum name _)     = name
      preDeclare :: Annotated Parse DeclRec -> Praxis (Praxis (Annotated KindCheck DeclRec))
      preDeclare (a@(src, _) :< decl) = case decl of
        DeclRecTerm declTerm -> return $ (\declTerm -> a :< DeclRecTerm declTerm) <$> generateDeclTerm declTerm
        DeclRecType declType -> do { kind <- freshKindUni; introCon src (declTypeName declType) kind; return ((\declType -> a :< DeclRecType declType) <$> generateDeclType' (Just kind) declType) }

  _ -> recurseTerm generate decl


generateDeclType :: Annotated Parse DeclType -> Praxis (Annotated KindCheck DeclType)
generateDeclType = generateDeclType' Nothing

generateDeclType' :: Maybe (Annotated KindCheck Kind) -> Annotated Parse DeclType -> Praxis (Annotated KindCheck DeclType)
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
        kind <- freshKindUni
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
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          , ("Copy",           deduce copy)
          , ("Capture",        deduce capture)
          ]
        DataBoxed -> Map.fromList
          [ ("Clone",          deduce clone)
          , ("Dispose",        deduce dispose)
          ]

    checkState . instanceEnv %= Map.insert name instances
    return $ (src, kind) :< DeclTypeData mode name args alts

  DeclTypeEnum name alts -> do
    let kind = phantom KindType
    introCon src name kind
    let
      instances = Map.fromList
        [ ("Clone",   \_ -> (Trivial, IsInstance))
        , ("Dispose", \_ -> (Trivial, IsInstance))
        , ("Copy",    \_ -> (Trivial, IsInstance))
        , ("Capture", \_ -> (Trivial, IsInstance))
        ]
    checkState . instanceEnv %= Map.insert name instances
    return $ (src, kind) :< DeclTypeEnum name alts


generateDeclTerm :: Annotated Parse DeclTerm -> Praxis (Annotated KindCheck DeclTerm)
generateDeclTerm (a@(src, _) :< decl) = ((src, ()) :<) <$> case decl of

  DeclTermVar name (Just sig@((src, _) :< qTy@(Forall vs _ _))) exp -> scope $ do
    checkDistinct src vs
    sig <- ((src, ()) :<) <$> recurseTerm generate qTy
    exp <- generate exp
    return $ DeclTermVar name (Just sig) exp

  _ -> recurseTerm generate decl


generateQType :: Annotated Parse QType -> Praxis (Annotated KindCheck  QType)
generateQType (a@(src, _) :< qTy) = ((src, ()) :<) <$> case qTy of

  Forall vs _ _ -> checkDistinct src vs >> (scope $ recurseTerm generate qTy)

  _             -> recurseTerm generate qTy
