module Token
  ( Token(..)
  ) where

import           Common
import           Pretty
import           Term   (Lit (..), QString (..))

data Token = QVarId QString
           | QConId QString
           | QVarSym QString
           | QConSym QString
           | ReservedCon String
           | ReservedOp String
           | ReservedId String
           | Lit Lit
           | Print (Printable String)
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
  pretty (Print (Printable p)) = Printable (Style Italic . Fg grey . p)
  pretty x = pretty $ case x of
    QVarId q      -> Fg white $ Value $ show q
    QConId q      -> Fg yellow $ Value $ show q
    QVarSym q     -> Fg red $ Value $ show q
    QConSym q     -> Fg white $ Value $ show q
    ReservedCon s -> Fg yellow $ Value s
    ReservedOp s  -> Fg purple $ Value s
    ReservedId s  -> Style Bold $ Fg blue $ Value s
    Lit l         -> Fg green $ Value $ show l
    Special c     -> Fg cyan $ Value [c]
    Uni s         -> Fg orange $ Value s
