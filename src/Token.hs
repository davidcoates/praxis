module Token
  ( Form(..)
  , isLower
  , isSymbol
  , isUpper
  , Token(..)
  ) where

import           Common
import qualified Data.Monoid.Colorful as Colored
import           Term                 (Flavor (..), Lit (..))


data Form = Lower | Symbol | Upper
  deriving Eq

isLower :: Char -> Bool
isLower  = (`elem` ['a'..'z'])

isSymbol :: Char -> Bool
isSymbol = (`elem` ("!#$%&*+/<=>?@\\^|-~:[]." :: [Char]))

isUpper :: Char -> Bool
isUpper  = (`elem` ['A'..'Z'])

data Token
  = Annotation (Colored String)
  | Ident Flavor Form String
  | Internal (Colored String)
  | Keyword Form String
  | Layout Char
  | Lit Lit
  | Special Char
  deriving Eq

unstyle :: Colored a -> Colored a
unstyle x = case x of
  Colored.Nil       -> Colored.Nil
  Colored.Value x   -> Colored.Value x
  Colored.Style _ x -> unstyle x
  Colored.Fg c x    -> Colored.Fg c (unstyle x)
  Colored.Bg c x    -> Colored.Bg c (unstyle x)
  Colored.Pair x y  -> Colored.Pair (unstyle x) (unstyle y)

highlight = RGB 216 213 199

instance Pretty Token where
  pretty token = pretty $ case token of
    Annotation str
      | null str          -> Colored.Nil
      | otherwise         -> Colored.Fg Black (Colored.Bg highlight ("[" <> unstyle str <> "]"))
    Ident Plain _     str -> Colored.Value str
    Ident Ref   Lower str -> Colored.Fg Yellow $ Colored.Value ('&':str)
    Ident Value Lower str -> Colored.Fg Cyan $ Colored.Value  ('!':str)
    Ident View  Lower str -> Colored.Fg Magenta $ Colored.Value ('?':str)
    Internal str          -> Colored.Style Underline $ unstyle str
    Keyword Lower  str    -> Colored.Style Bold $ Colored.Value str
    Keyword Symbol str    -> Colored.Fg Green $ Colored.Value str
    Keyword Upper  str    -> Colored.Style Bold $ Colored.Value str
    Layout char           -> Colored.Fg Red $ Colored.Value [char]
    Lit lit               -> Colored.Fg Blue $ Colored.Value $ show lit
    Special char          -> Colored.Fg Black $ Colored.Value [char]

instance Pretty (Sourced Token) where
  pretty (_ :< x) = pretty x
