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
           | Uni String
  deriving Eq

red    = RGB 252 146 158
orange = RGB 255 169 110
yellow = RGB 250 200 99
green  = RGB 141 200 145
cyan   = RGB 136 198 190
blue   = RGB 121 182 242
purple = RGB 197 165 197
grey   = RGB 242 242 242
white  = RGB 255 255 255

instance Pretty Token where
  pretty x = case x of
    QVarId q      -> Fg white $ plain $ show q
    QConId q      -> Fg yellow $ plain $ show q
    QVarSym q     -> Fg red $ plain $ show q
    QConSym q     -> Fg white $ plain $ show q
    ReservedCon s -> Fg yellow $ plain s
    ReservedOp s  -> Fg purple $ plain s
    ReservedId s  -> Style Bold $ Fg blue $ plain s
    Lit l         -> Fg green $ plain $ show l
    Print x       -> Style Italic $ Fg grey $ x
    Special c     -> Fg cyan $ plain [c]
    Uni s         -> Fg orange $ plain s
