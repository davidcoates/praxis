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
           | Print String
           | Special Char
  deriving Eq

instance Show Token where
  show x = case x of
    QVarId q      -> show q
    QConId q      -> show q
    QVarSym q     -> show q
    QConSym q     -> show q
    ReservedCon s -> s
    ReservedOp s  -> s
    ReservedId s  -> s
    Lit l         -> show l
    Print s       -> s
    Special c     -> [c]
