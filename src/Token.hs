module Token
  ( Token(..)
  ) where

import           Common
import qualified Data.Monoid.Colorful as Color
import           Term                 (Lit (..), ViewDomain (..))

data Token = QVarId (Qualified Name)
           | QConId (Qualified Name)
           | QVarSym (Qualified Name)
           | QConSym (Qualified Name)
           | ReservedCon String
           | ReservedOp String
           | ReservedId String
           | Layout Char
           | Lit Lit
           | Annotation (Printable String)
           | Special Char
           | Uni String -- ^ A unification variable
  deriving Eq

unstyle :: Colored a -> Colored a
unstyle x = case x of
  Nil            -> Nil
  Value x        -> Value x
  Style _ x      -> unstyle x
  Fg c x         -> Fg c (unstyle x)
  Bg c x         -> Bg c (unstyle x)
  Color.Pair x y -> Color.Pair (unstyle x) (unstyle y)

highlight = RGB 216 213 199

instance Pretty Token where
  pretty (Annotation (Printable p)) = Printable (\opt -> let s = p opt in if null s then Nil else Fg Black (Bg highlight (Value "[" <> unstyle s <> Value "]")))
  pretty x = pretty $ case x of
    QVarId q      -> Value $ show q
    QConId q      -> Value $ show q
    QVarSym q     -> Value $ show q
    QConSym q     -> Value $ show q
    ReservedCon s -> Value s
    ReservedOp s  -> Fg Green $ Value s
    ReservedId s  -> Style Bold $ Value s
    Layout c      -> Fg DullRed $ Value [c]
    Lit l         -> Fg Blue $ Value $ show l
    Special c     -> Fg Black $ Value [c]
    Uni s         -> Fg Magenta $ Value s
