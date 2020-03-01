module Stage
  ( Stage(..)
  , Check(..)
  ) where

data Stage = Unknown
           | Tokenise
           | Layout
           | Parse
           | Desugar
           | KindCheck Check
           | TypeCheck Check
           | Evaluate

data Check = Warmup
           | Generate
           | Solve

instance Show Stage where
  show = \case
    Unknown     -> "Unknown"
    Tokenise    -> "Tokenise"
    Layout      -> "Tokenise (Layout)"
    Parse       -> "Parse"
    Desugar     -> "Parse (Desugar)"
    KindCheck c -> "Kind Check" ++ show c
    TypeCheck c -> "Type Check" ++ show c
    Evaluate    -> "Evaluate"

instance Show Check where
  show = \case
    Warmup   -> ""
    Generate -> " (Constraint Generator)"
    Solve    -> " (Constraint Solver)"
