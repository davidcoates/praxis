module Stage
  ( Stage(..)
  ) where

data Stage = Unknown
           | Parse
           | KindCheck
           | TypeCheck
           | Evaluate

instance Show Stage where
  show = \case
    Unknown     -> "unknown"
    Parse       -> "parse"
    KindCheck   -> "kind check"
    TypeCheck   -> "type check"
    Evaluate    -> "evaluate"
