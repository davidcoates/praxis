Keep prefix negation but change operator sections?
(_ - 2) for operator seciton, (-2) for negate 2 ?

Subexpression with type parameters that don't appear in superexpression
e.g., length [undefined] :: Int
[undefined] :: a

Type defaulting is bad. In haskell it is mostly done for Num.
How to avoid but still have nice numeric literals?
Int vs Integer for literals , right now it isn't consistent.


To avoid linear functions, functions shouldn't capture linear types.
So we can share and drop functions.
This applies to constructs as well.
Note: (x,y) desugars to a record say
data Pair a b = Pair { fst :: a, snd :: b }

(x,) isn't a thing? We could instead write 
\y -> Pair { fst = x, snd = y }
Or Pair { fst = x, snd = _ } ? 


(x,y) doesn't desugar to
data Pair a b = Pair a b
because then  Pair :: forall a b. (Share a, Drop a) => a -> b -> Pair a b

What about List?
data List a = (:) a (List a)
or
data List a = List { head :: a, tail :: List a }


For single-alternative data, how should lenses work?

So
data Pair a b = Pair { fst :: a, snd :: b }

want
fst :: Lens a (Pair a b)
so we would say
fst a in Pair a b ?

Or:
type Pair a b = { fst :: a, snd :: b }
i.e., do we really need it to be data?



The type of generalised functions must be known before use.
Requiring all top-level functions to have type signatures would guarantee this.

Should top-level functions be shareable and discardable?
Should be top pure.
Top pure even after instantiation.
