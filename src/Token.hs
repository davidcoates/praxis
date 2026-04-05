module Token
  ( Form(..)
  , Keyword(..)
  , keywordForm
  , keywordString
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

data Keyword
  -- Lower
  = KeywordRead | KeywordIn | KeywordIf | KeywordThen | KeywordElse
  | KeywordUsing | KeywordDatatype | KeywordEnum | KeywordCases | KeywordCase | KeywordOf
  | KeywordWhere | KeywordDo | KeywordForall | KeywordLet | KeywordOperator
  | KeywordSwitch | KeywordRec | KeywordDefer | KeywordSeq
  -- Upper (kinds)
  | KeywordType | KeywordRef | KeywordView
  -- Upper (instances)
  | KeywordClone | KeywordDispose | KeywordCopy | KeywordCapture | KeywordIntegral
  -- Symbol
  | KeywordColon | KeywordEquals | KeywordLambda | KeywordArrow | KeywordAt
  deriving (Eq, Ord, Enum, Bounded)

keywordString :: Keyword -> String
keywordString = \case
  KeywordRead     -> "read"
  KeywordIn       -> "in"
  KeywordIf       -> "if"
  KeywordThen     -> "then"
  KeywordElse     -> "else"
  KeywordUsing    -> "using"
  KeywordDatatype -> "datatype"
  KeywordEnum     -> "enum"
  KeywordCases    -> "cases"
  KeywordCase     -> "case"
  KeywordOf       -> "of"
  KeywordWhere    -> "where"
  KeywordDo       -> "do"
  KeywordForall   -> "forall"
  KeywordLet      -> "let"
  KeywordOperator -> "operator"
  KeywordSwitch   -> "switch"
  KeywordRec      -> "rec"
  KeywordDefer    -> "defer"
  KeywordSeq      -> "seq"
  KeywordType     -> "Type"
  KeywordRef      -> "Ref"
  KeywordView     -> "View"
  KeywordClone    -> "Clone"
  KeywordDispose  -> "Dispose"
  KeywordCopy     -> "Copy"
  KeywordCapture  -> "Capture"
  KeywordIntegral -> "Integral"
  KeywordColon    -> ":"
  KeywordEquals   -> "="
  KeywordLambda   -> "\\"
  KeywordArrow    -> "->"
  KeywordAt       -> "@"

keywordForm :: Keyword -> Form
keywordForm kw = case keywordString kw of
  (c:_) | isLower c -> Lower
        | isUpper c -> Upper
        | otherwise -> Symbol

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
  | Keyword Keyword
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
    Ident Ref   Lower str -> Colored.Fg Yellow  $ Colored.Value ('&':str)
    Ident Value Lower str -> Colored.Fg Cyan    $ Colored.Value ('!':str)
    Ident View  Lower str -> Colored.Fg Magenta $ Colored.Value ('?':str)
    Internal str          -> Colored.Style Underline $ unstyle str
    Keyword kw -> case keywordForm kw of
      Lower  -> Colored.Style Bold $ Colored.Value (keywordString kw)
      Symbol -> Colored.Fg Green   $ Colored.Value (keywordString kw)
      Upper  -> Colored.Style Bold $ Colored.Value (keywordString kw)
    Layout char           -> Colored.Fg Red $ Colored.Value [char]
    Lit lit               -> Colored.Fg Blue $ Colored.Value $ show lit
    Special char          -> Colored.Fg Black $ Colored.Value [char]

instance Pretty (Sourced Token) where
  pretty (_ :< x) = pretty x
