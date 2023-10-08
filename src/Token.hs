module Token
  ( Token(..)
  ) where

import           Common
import           Term   (Lit (..), TyOpDomain (..))

data Token = QVarId (Qualified Name)
           | QConId (Qualified Name)
           | QVarSym (Qualified Name)
           | QConSym (Qualified Name)
           | ReservedCon String
           | ReservedOp String
           | ReservedId String
           | Layout Char
           | Lit Lit
           | Print (Printable String)
           | Special Char
           | Uni String -- A unification variable
           | Annotation (Printable String)
  deriving Eq

hint     = RGB 0xDE 0xFB 0xFF
white    = RGB 0xEE 0xEE 0xEC
grey     = RGB 0xAA 0xAA 0xAA
darkGrey = RGB 0x88 0x88 0x88
teal     = RGB 0x39 0xCC 0xCC
yellow   = RGB 0xFC 0xBA 0x03
green    = RGB 0x55 0x94 0x4E
pink     = RGB 0xF7 0x91 0x83
blue     = RGB 0x80 0x80 0xF0
orange   = RGB 0xFF 0xCF 0xBD
purple   = RGB 0xF9 0xD4 0xFF

instance Pretty Token where
  pretty (Print (Printable p)) = Printable (Style Italic . Fg hint . p)
  pretty x = pretty $ Unstyle Italic $ case x of
    QVarId q      -> Fg white $ Value $ show q
    QConId q      -> Fg yellow $ Value $ show q
    QVarSym q     -> Fg white $ Value $ show q
    QConSym q     -> Fg yellow $ Value $ show q
    ReservedCon s -> Fg blue $ Value s
    ReservedOp s  -> Fg pink $ Value s
    ReservedId s  -> Fg teal $ Value s
    Layout c      -> Fg darkGrey $ Value [c]
    Lit l         -> Fg green $ Value $ show l
    Special c     -> Fg grey $ Value [c]
    Uni s         -> Fg orange $ Value s
