module Stage
  ( Stage(..)
  , Check(..)
  ) where

data Stage = Unknown
           | Tokenise
           | Layout
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
    Layout      -> "Tokenise (Layout)"
    Parse       -> "Parse"
    Desugar     -> "Parse (Desugar)"
    TypeCheck c -> "Type Check " ++ show c
    KindCheck c -> "Kind Check " ++ show c
    Evaluate    -> "Evaluate"

instance Show Check where
  show s = case s of
    Warmup   -> ""
    Generate -> "(Constraint Generator)"
    Solve    -> "(Constraint Solver)"
