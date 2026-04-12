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
  | Lower
  | Evaluate
  deriving Eq

instance Show Stage where
  show = \case
    Initial   -> "initial"
    Parse     -> "parse"
    KindCheck -> "kind check"
    TypeCheck -> "type check"
    Lower     -> "lower"
    Evaluate  -> "evaluate"

data StageT (s :: Stage) where
  InitialT   :: StageT Initial
  ParseT     :: StageT Parse
  KindCheckT :: StageT KindCheck
  TypeCheckT :: StageT TypeCheck
  LowerT     :: StageT Lower
  EvaluateT  :: StageT Evaluate

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

instance IsStage Lower where
  stageT = LowerT

instance IsStage Evaluate where
  stageT = EvaluateT

stageToEnum :: StageT s -> Stage
stageToEnum = \case
  InitialT   -> Initial
  ParseT     -> Parse
  KindCheckT -> KindCheck
  TypeCheckT -> TypeCheck
  LowerT     -> Lower
  EvaluateT  -> Evaluate
