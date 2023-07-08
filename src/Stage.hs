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
    Unknown     -> "unknown"
    Tokenise    -> "tokenise"
    Layout      -> "tokenise (layout)"
    Parse       -> "parse"
    Desugar     -> "parse (desugar)"
    KindCheck c -> "kind check" ++ show c
    TypeCheck c -> "type check" ++ show c
    Evaluate    -> "evaluate"

instance Show Check where
  show = \case
    Warmup   -> ""
    Generate -> " (constraint generator)"
    Solve    -> " (constraint solver)"
