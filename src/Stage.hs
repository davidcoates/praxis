module Stage
  ( Stage(..)
  , Check(..)
  ) where

data Stage = Unknown
           | Tokenise
           | Layout
           | Parse
           | Desugar
           | Rewrite
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
    Layout      -> "layout"
    Parse       -> "parse"
    Desugar     -> "desugar"
    Rewrite     -> "rewrite"
    KindCheck c -> "kind check" ++ show c
    TypeCheck c -> "type check" ++ show c
    Evaluate    -> "evaluate"

instance Show Check where
  show = \case
    Warmup   -> ""
    Generate -> " (constraint generator)"
    Solve    -> " (constraint solver)"
