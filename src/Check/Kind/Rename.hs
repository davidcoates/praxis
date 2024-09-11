{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

module Check.Kind.Rename
  ( run
  ) where


import qualified Check.Rename as Check
import           Check.State
import           Common
import           Introspect
import           Praxis
import           Print
import           Term


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- rename term
  display term `ifFlag` debug
  return term

rename :: Term a => Annotated a -> Praxis (Annotated a)
rename term = ($ term) $ case typeof (view value term) of
  IDeclTerm -> renameDeclTerm
  IDeclType -> renameDeclType
  IType     -> renameType
  ITypeVar  -> renameTypeVar
  IQType    -> renameQType
  _         -> value (recurseTerm rename)


disambiguate :: Source -> Name -> Praxis Name
disambiguate = Check.disambiguate kindCheckState

intro :: Name -> Praxis Name
intro = Check.intro kindCheckState

introMany :: Source -> [Name] -> Praxis [Name]
introMany = Check.introMany kindCheckState

introFromQType :: Annotated QType -> Praxis ()
introFromQType ((src, _) :< qTy) = case qTy of
  Forall vs _ _ -> do
    introMany src (map typeVarName vs)
    return ()
  Mono _ -> return ()

renameDeclTerm :: Annotated DeclTerm -> Praxis (Annotated DeclTerm)
renameDeclTerm (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermVar name sig exp -> do
    case sig of
      Nothing  -> recurseTerm rename decl
      Just sig -> save (kindCheckState . scopes) $ introFromQType sig >> (DeclTermVar name <$> (Just <$> recurse rename sig) <*> recurse rename exp)

  _ -> recurseTerm rename decl


renameDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
renameDeclType (a@(src, _) :< decl) = (a :< ) <$> case decl of

  DeclTypeData _ _ typeVars _ -> save (kindCheckState . scopes) $ introMany src (map typeVarName typeVars) >> recurseTerm rename decl

  _ -> recurseTerm rename decl


renameType :: Annotated Type -> Praxis (Annotated Type)
renameType (a@(src, _) :< ty) = (a :<) <$> case ty of

  TypeVarPlain n  -> TypeVarPlain <$> disambiguate src n

  TypeVarValue n  -> TypeVarValue <$> disambiguate src n

  TypeOpVarRef n  -> TypeOpVarRef <$> disambiguate src n

  TypeOpVarView n -> TypeOpVarView <$> disambiguate src n

  _               -> recurseTerm rename ty


renameTypeVar :: Annotated TypeVar -> Praxis (Annotated TypeVar)
renameTypeVar (a@(src, _) :< typeVar) = (a :<) <$> case typeVar of

  TypeVarVarPlain n -> TypeVarVarPlain <$> disambiguate src n

  TypeVarVarRef n   -> TypeVarVarRef <$> disambiguate src n

  TypeVarVarValue n -> TypeVarVarValue <$> disambiguate src n

  TypeVarVarView n  -> TypeVarVarView <$> disambiguate src n


renameQType :: Annotated QType -> Praxis (Annotated QType)
renameQType qTy = save (kindCheckState . scopes) $ introFromQType qTy >> recurse rename qTy
