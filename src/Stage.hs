module Stage
  ( Stage(..)
  , Check(..)
  , Parse
  , TypeCheck
  , KindCheck
  ) where

data Stage = Unknown
           | Tokenise
           | Parse
           | Desugar
           | TypeCheck Check
           | KindCheck Check
           | Evaluate

data Check = Warmup
           | Generate
           | Solve

instance Show Stage where
  show s = case s of
    Unknown     -> "Unknown"
    Tokenise    -> "Tokenise"
    Parse       -> "Parse"
    Desugar     -> "Desugar"
    TypeCheck c -> "Type Check " ++ show c
    KindCheck c -> "Kind Check " ++ show c
    Evaluate    -> "Evaluate"

instance Show Check where
  show s = case s of
    Warmup   -> ""
    Generate -> "(Constraint Generator)"
    Solve    -> "(Constraint Solver)"

-- Annotation stages
data Parse     = Parse_
data TypeCheck = TypeCheck_
data KindCheck = KindCheck_
