module Check.Type.Check
  ( check
  ) where

import           Annotate
import           Check.Type.Generate
import           Check.Type.Require
import           Check.Type.Solve
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Type

check :: Recursive a => Parsed a -> Praxis (Typed a)
check a = save stage $ do
  stage .= TypeCheck Warmup
  our .= initialSystem
  a' <- generate a
  ts <- solve
  let r = sub (\t -> case t of { TyUni n -> lookup n ts; _ -> Nothing }) a'
  output $ r
  return r
  -- TODO FIXME add defaulting (need to wait until after kinds?)
