{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Check.Type.Annotate
  ( Typed
  )
  where

import           Check.Type.Constraint
import           Common
import           Introspect
import           Stage                 (TypeCheck)

type Typed a = Annotated TypeCheck a

-- TODO incomplete
-- TODO use records

type instance Annotation TypeCheck (Const Constraint) = Derivation -- TODO should this be here?

type instance Annotation TypeCheck DataAlt = ()
type instance Annotation TypeCheck Decl = Typed Type
type instance Annotation TypeCheck Exp = (Typed Type, Typed Type)
type instance Annotation TypeCheck Pat = Typed Type
type instance Annotation TypeCheck Program = ()
type instance Annotation TypeCheck QType = ()
type instance Annotation TypeCheck Stmt = Typed Type
type instance Annotation TypeCheck TyPat = ()
type instance Annotation TypeCheck Type = ()

instance Complete TypeCheck where
  complete f i a = case i of
    IDataAlt -> pure ()
    IDecl    -> f a
    IExp     -> both f a
    IPat     -> f a
    IProgram -> pure ()
    IQType   -> pure ()
    IStmt    -> f a
    ITyPat   -> pure ()
    IType    -> pure ()

