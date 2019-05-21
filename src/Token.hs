module Token
  ( Token(..)
  ) where

import           AST    (Lit (..), QString (..))
import           Common

data Token = QVarId QString
           | QConId QString
           | QVarSym QString
           | QConSym QString
           | ReservedCon String
           | ReservedOp String
           | ReservedId String
           | Lit Lit
           | Print (Colored String)
           | Special Char
  deriving Eq

instance Pretty Token where
  pretty x = case x of
    QVarId q      -> plain $ show q
    QConId q      -> Fg Green $ plain $ show q
    QVarSym q     -> plain $ show q
    QConSym q     -> plain $ show q
    ReservedCon s -> Fg Magenta $ plain s
    ReservedOp s  -> Fg Magenta $ plain s
    ReservedId s  -> Style Bold $ Fg Yellow $ plain s
    Lit l         -> Fg Cyan $ plain $ show l
    Print x       -> Style Italic $ Fg White $ x
    Special c     -> plain [c]
