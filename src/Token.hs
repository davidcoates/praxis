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
           | TyOpVar String
           | Uni String
  deriving Eq

hint    = RGB 0xDE 0xFB 0xFF
white   = RGB 0xEE 0xEE 0xEC
grey    = RGB 0xAA 0xAA 0xAA
teal    = RGB 0x39 0xCC 0xCC
yellow  = RGB 0xFC 0xBA 0x03
green   = RGB 0x55 0x94 0x4E
pink    = RGB 0xF7 0x91 0x83
blue    = RGB 0xCC 0xFF 0xF0
orange  = RGB 0xFF 0xCF 0xBD
purple  = RGB 0xF9 0xD4 0xFF

instance Pretty Token where
  pretty (Print (Printable p)) = Printable (Style Italic . Fg hint . p)
  pretty x = pretty $ case x of
    QVarId q      -> Fg white $ Value $ show q
    QConId q      -> Fg yellow $ Value $ show q
    QVarSym q     -> Fg teal $ Value $ show q
    QConSym q     -> Fg white $ Value $ show q
    ReservedCon s -> Fg blue $ Value s
    ReservedOp s  -> Fg pink $ Value s
    ReservedId s  -> Style Bold $ Fg white $ Value s
    Lit l         -> Fg green $ Value $ show l
    Special c     -> Fg grey $ Value [c]
    TyOpVar s     -> Fg purple $ Value ('?' : s)
    Uni s         -> Fg orange $ Value s
