-- Type checker

module Check
  ( check
  ) where

import           Check.Generate (generate)
import           Check.Solve    (solve)
import           Compiler
import           Tag
import           Type           (subsImpure)

check :: Compiler ()
check = save stage $ do
  set stage Check
  cs <- generate
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  e <- get typedAST
  let e' = tagMap (\(t, s) -> (subsImpure ft fe <$> t, s)) e
  set typedAST e'
  debugPrint e'
