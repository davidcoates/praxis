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
  display "renamed term" term `ifFlag` debug
  return term

rename :: Term a => Annotated a -> Praxis (Annotated a)
rename term = ($ term) $ case typeof (view value term) of
  IDeclTerm -> renameDeclTerm
  IDeclType -> renameDeclType
  IType     -> renameType
  ITypeVar  -> renameTypeVar
  IQType    -> renameQType
  _         -> value (recurseTerm rename)


disambiguate :: Source -> (Flavor, Name) -> Praxis Name
disambiguate = Check.disambiguate kindCheckState

intro :: (Flavor, Name) -> Praxis Name
intro = Check.intro kindCheckState

introMany :: Source -> [(Flavor, Name)] -> Praxis [Name]
introMany = Check.introMany kindCheckState

introFromQType :: Annotated QType -> Praxis ()
introFromQType ((src, _) :< qTy) = case qTy of

  Forall vs _ _ -> do
    introMany src (map (\(_ :< TypeVarVar f n) -> (f, n)) vs)
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

  DeclTypeData _ _ typeVars _ -> save (kindCheckState . scopes) $ introMany src (map (\(_ :< TypeVarVar f n) -> (f, n)) typeVars) >> recurseTerm rename decl

  _ -> recurseTerm rename decl


renameType :: Annotated Type -> Praxis (Annotated Type)
renameType (a@(src, _) :< ty) = (a :<) <$> case ty of

  TypeVar f n -> TypeVar f <$> disambiguate src (f, n)

  _           -> recurseTerm rename ty


renameTypeVar :: Annotated TypeVar -> Praxis (Annotated TypeVar)
renameTypeVar (a@(src, _) :< TypeVarVar f n) = (\n -> a :< TypeVarVar f n) <$> disambiguate src (f, n)

renameQType :: Annotated QType -> Praxis (Annotated QType)
renameQType qTy = save (kindCheckState . scopes) $ introFromQType qTy >> recurse rename qTy
