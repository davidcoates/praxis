{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Stage
  ( Stage(..)
  , StageT(..)
  , IsStage(..)
  , stageToEnum
  ) where


data Stage
  = Initial
  | Parse
  | KindCheck
  | TypeCheck
  | Monomorphize
  | Evaluate
  deriving Eq

instance Show Stage where
  show = \case
    Initial      -> "initial"
    Parse        -> "parse"
    KindCheck    -> "kind check"
    TypeCheck    -> "type check"
    Monomorphize -> "monomorphize"
    Evaluate     -> "evaluate"

data StageT (s :: Stage) where
  InitialT      :: StageT Initial
  ParseT        :: StageT Parse
  KindCheckT    :: StageT KindCheck
  TypeCheckT    :: StageT TypeCheck
  MonomorphizeT :: StageT Monomorphize
  EvaluateT     :: StageT Evaluate

class IsStage (s :: Stage) where
  stageT :: StageT s

instance IsStage Initial where
  stageT = InitialT

instance IsStage Parse where
  stageT = ParseT

instance IsStage KindCheck where
  stageT = KindCheckT

instance IsStage TypeCheck where
  stageT = TypeCheckT

instance IsStage Monomorphize where
  stageT = MonomorphizeT

instance IsStage Evaluate where
  stageT = EvaluateT

stageToEnum :: StageT s -> Stage
stageToEnum = \case
  InitialT      -> Initial
  ParseT        -> Parse
  KindCheckT    -> KindCheck
  TypeCheckT    -> TypeCheck
  MonomorphizeT -> Monomorphize
  EvaluateT     -> Evaluate
