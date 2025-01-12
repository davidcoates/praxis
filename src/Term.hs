{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE Strict               #-}
{-# LANGUAGE StrictData           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators        #-}


module Term
  -- | Operators
  ( Assoc(..)
  , Op(..)
  , OpRules(..)
  , Prec(..)

  -- | T0
  , Bind(..)
  , DataCon(..)
  , DataMode(..)
  , Decl(..)
  , DeclRec(..)
  , DeclTerm(..)
  , DeclType(..)
  , Exp(..)
  , Lit(..)
  , Pat(..)
  , Program(..)
  , Specialization
  , Stmt(..)
  , Tok(..)

  -- | T1
  , Flavor(..)
  , QType(..)
  , TypeConstraint(..)
  , Type(..)
  , TypePat(..)

  -- | T2
  , Kind(..)
  , KindConstraint(..)

  -- | Solver
  , Requirement(..)
  , TypeReason(..)
  , KindReason(..)

  , Annotation
  , Annotated
  , source
  , annotation
  , phantom

  , isTypeOp
  ) where

import           Common
import           Stage

import           Data.Set (Set)

-- * OPERATORS *

data Assoc = AssocLeft | AssocRight
  deriving (Eq, Ord)

data Op (s :: Stage) = Op [Maybe Name] -- TDO qualification over this
  deriving (Eq, Ord)

data OpRules (s :: Stage) = OpRules [Either Assoc [Annotated s Prec]]
  deriving (Eq, Ord)

data Prec (s :: Stage) = Prec Ordering (Annotated s Op)
  deriving (Eq, Ord)


-- * DECLARATIONS & EXPRESSIONS *

data Bind (s :: Stage) = Bind (Annotated s Pat) (Annotated s Exp)
  deriving (Eq, Ord)

data DataCon (s :: Stage) = DataCon Name (Annotated s Type)
  deriving (Eq, Ord)

data DataMode = DataUnboxed | DataBoxed
  deriving (Eq, Ord)

data Decl (s :: Stage)
  = DeclOpSugar (Annotated s Op) Name (Annotated s OpRules)
  | DeclRec [Annotated s DeclRec]
  | DeclSynSugar Name (Annotated s Type)
  | DeclTerm (Annotated s DeclTerm)
  | DeclType (Annotated s DeclType)
  deriving (Eq, Ord)

data DeclRec (s :: Stage)
  = DeclRecTerm (Annotated s DeclTerm)
  | DeclRecType (Annotated s DeclType)
  deriving (Eq, Ord)

data DeclType (s :: Stage)
  = DeclTypeData DataMode Name [Annotated s TypePat] [Annotated s DataCon]
  | DeclTypeDataSugar (Maybe DataMode) Name [Annotated s TypePat] [Annotated s DataCon]
  | DeclTypeEnum Name [Name]
  deriving  (Eq, Ord)

data DeclTerm (s :: Stage)
  = DeclTermVar Name (Maybe (Annotated s QType)) (Annotated s Exp)
  | DeclTermDefSugar Name [Annotated s Pat] (Annotated s Exp)
  | DeclTermSigSugar Name (Annotated s QType)
  deriving (Eq, Ord)

-- TODO constraints
type Specialization (s :: Stage) = [(Annotated s TypePat, Annotated s Type)]

data Exp (s :: Stage)
  = Apply (Annotated s Exp) (Annotated s Exp)
  | Case (Annotated s Exp) [(Annotated s Pat, Annotated s Exp)]
  | Cases [(Annotated s Pat, Annotated s Exp)]
  | Capture [(Name, Annotated s QType)] (Annotated s Exp)
  | Con Name
  | Defer (Annotated s Exp) (Annotated s Exp)
  | DoSugar [Annotated s Stmt]
  | If (Annotated s Exp) (Annotated s Exp) (Annotated s Exp)
  | Lambda (Annotated s Pat) (Annotated s Exp)
  | Let (Annotated s Bind) (Annotated s Exp)
  | Lit Lit
  | MixfixSugar [Annotated s Tok]
  | Read Name (Annotated s Exp)
  | Pair (Annotated s Exp) (Annotated s Exp)
  | Seq (Annotated s Exp) (Annotated s Exp)
  | Sig (Annotated s Exp) (Annotated s Type)
  | Specialize (Annotated s Exp) (Specialization s)
  | Switch [(Annotated s Exp, Annotated s Exp)]
  | Unit
  | Var Name
  | VarRefSugar Name
  | Where (Annotated s Exp) [Annotated s DeclTerm]
  deriving (Eq, Ord)

-- TODO: Array literals?
data Lit
  = Bool Bool
  | Char Char
  | Integer Integer
  | String String
  deriving (Eq, Ord)

-- TODO remove?
instance Show Lit where
  show = \case
    Bool b    -> show b
    Char c    -> show c
    Integer i -> show i
    String s  -> show s

data Pat (s :: Stage)
  = PatAt Name (Annotated s Pat)
  | PatData Name (Annotated s Pat)
  | PatEnum Name
  | PatHole
  | PatLit Lit
  | PatPair (Annotated s Pat) (Annotated s Pat)
  | PatUnit
  | PatVar Name
  deriving (Eq, Ord)

data Program (s :: Stage) = Program [Annotated s Decl]
  deriving (Eq, Ord)

data Stmt (s :: Stage)
  = StmtBind (Annotated s Bind)
  | StmtExp (Annotated s Exp)
  deriving (Eq, Ord)

data Tok (s :: Stage)
  = TokExp (Annotated s Exp)
  | TokOp Name
  deriving (Eq, Ord)

data Flavor = Plain | Ref | Value | View
  deriving (Eq, Ord)

data TypePat (s :: Stage) = TypePatVar Flavor Name
  deriving (Eq, Ord)

data Type (s :: Stage)
  = TypeApply (Annotated s Type) (Annotated s Type)
  | TypeApplyOp (Annotated s Type) (Annotated s Type)
  | TypeCon Name
  | TypeFn (Annotated s Type) (Annotated s Type)
  | TypeIdentityOp
  | TypePair (Annotated s Type) (Annotated s Type)
  | TypeRef Name
  | TypeSetOp (Set (Annotated s Type))
  | TypeUni Flavor Name
  | TypeUnit
  | TypeVar Flavor Name
  deriving (Eq, Ord)

data QType (s :: Stage)
  = Forall [Annotated s TypePat] [Annotated s TypeConstraint] (Annotated s Type)
  | Mono (Annotated s Type)
  deriving (Eq, Ord)

data Kind (s :: Stage)
  = KindUni Name
  | KindConstraint
  | KindFn (Annotated s Kind) (Annotated s Kind)
  | KindRef
  | KindType
  | KindView
  deriving (Eq, Ord)

data TypeConstraint (s :: Stage)
  = TypeIsEq (Annotated s Type) (Annotated s Type)
  | TypeIsEqIfAffine (Annotated s Type) (Annotated s Type) (Annotated s Type)
  | TypeIsInstance (Annotated s Type)
  | TypeIsIntegralOver (Annotated s Type) Integer
  | TypeIsRef (Annotated s Type)
  | TypeIsRefFree (Annotated s Type) Name
  | TypeIsSub (Annotated s Type) (Annotated s Type)
  | TypeIsSubIfAffine (Annotated s Type) (Annotated s Type) (Annotated s Type)
  | TypeIsValue (Annotated s Type)
  deriving (Eq, Ord)

data KindConstraint (s :: Stage)
  = KindIsEq (Annotated s Kind) (Annotated s Kind)
  | KindIsPlain (Annotated s Kind)
  | KindIsSub (Annotated s Kind) (Annotated s Kind)
  deriving (Eq, Ord)

newtype Requirement a (s :: Stage) = Requirement (Annotated s a)
  deriving (Eq, Ord)

type family Annotation (s :: Stage) a where
  Annotation KindCheck Type = Annotated KindCheck Kind
  Annotation KindCheck TypePat = Annotated KindCheck Kind
  Annotation KindCheck DeclType = Annotated KindCheck Kind
  Annotation KindCheck (Requirement KindConstraint) = KindReason
  Annotation TypeCheck DataCon = Annotated TypeCheck QType
  Annotation TypeCheck Exp = Annotated TypeCheck Type
  Annotation TypeCheck Pat = Annotated TypeCheck Type
  Annotation TypeCheck (Requirement TypeConstraint) = TypeReason
  Annotation s a = ()


type Annotated (s :: Stage) a = Tag (Source, Annotation s a) (a s)

source :: Functor f => (Source -> f Source) -> Annotated s a -> f (Annotated s a)
source = tag . first

annotation :: Functor f => (Annotation s a -> f (Annotation s a)) -> Annotated s a -> f (Annotated s a)
annotation = tag . second

phantom :: (Annotation s a ~ ()) => (a s) -> Annotated s a
phantom x = (Phantom, ()) :< x

data TypeReason
  = TypeReasonApply (Annotated TypeCheck Exp) (Annotated TypeCheck Exp)
  | TypeReasonBind (Annotated TypeCheck Pat) (Annotated TypeCheck Exp)
  | TypeReasonCaptured Name
  | TypeReasonCaseCongruence
  | TypeReasonConstructor Name
  | TypeReasonFunctionCongruence Name (Maybe (Annotated TypeCheck QType))
  | TypeReasonIfCondition
  | TypeReasonIfCongruence
  | TypeReasonIntegerLiteral Integer
  | TypeReasonMultiAlias Name
  | TypeReasonMultiUse Name
  | TypeReasonRead Name
  | TypeReasonSignature (Annotated TypeCheck Type)
  | TypeReasonSpecialization Name
  | TypeReasonSwitchCondition
  | TypeReasonSwitchCongruence
  deriving (Eq, Ord)

data KindReason
  = KindReasonData Name [Annotated KindCheck TypePat]
  | KindReasonDataCon (Annotated KindCheck DataCon)
  | KindReasonQType (Annotated KindCheck QType)
  | KindReasonTypeApply (Annotated KindCheck Type) (Annotated KindCheck Type)
  | KindReasonTypeApplyOp (Annotated KindCheck Type) (Annotated KindCheck Type)
  | KindReasonType (Annotated KindCheck Type)
  | KindReasonTypePat (Annotated KindCheck TypePat)
  deriving (Eq, Ord)

-- TODO what about TypeApply?
isTypeOp :: Annotated s Type -> Bool
isTypeOp t = case view value t of
  TypeIdentityOp -> True
  TypeRef _      -> True
  TypeSetOp _    -> True
  TypeUni Ref _  -> True
  TypeUni View _ -> True
  TypeVar Ref _  -> True
  TypeVar View _ -> True
  _              -> False
