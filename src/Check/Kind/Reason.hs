module Check.Kind.Reason
  ( Reason(..)
  ) where

data Reason = AppType
            | Custom String -- TODO get rid of Custom and Unknown
            | Unknown

instance Show Reason where
  show = \case
    AppType  -> "Type application"
    Custom s -> s
    Unknown  -> "<Unknown>"
