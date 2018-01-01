Main points:
- Strict by default
- Mostly pure but explicit impure code with effect types
- Linear types (typically abstract) for pure destructive updates

Secondary features:
- Strictness allows aggressive unboxing
- Only tuples are () and (a, b). (a, b, c) desugars to (a, (b, c)). Avoids tuple class hell.
- In-built lenses for records? Would require Rank2 type support (bad)

Possible other features:
- Row-polymorphic records/variants
- Better manipulation of modules
- Rebindable syntax, Mixfix?
- Abstract types (Specify co/contra variance?)


Value of linear type must be used exactly once. Allows for PURE destructive updates.
let
  a = Array 0 100 -- Array of 100 0's
  b = update a 5 550 -- Perform destructive update of a
in
  b
  ^-- If we instead returned (a, b), then we would introduce side effect (a is mutated)

Some terms:
Linear = must be used exactly once. Linear = Affine + Relevant
Affine = must be used no more than once.
Relevant = must be used at least once.
For pure destructive updates, most important thing is Affine.

Shareable == Not affine.
Discardable == Not relevant.

-- For abstract types implementing an explicit copy constructor
class Copy a where
  copy :: a! -> a
a! == read only reference to a

-- For abstract types implementing an explicit destructor
class Kill a where
  kill :: a -> ()

-- Special Share class. A value of a shareable type can be used multiple times.
-- Compiler implcitly inserts 'copy' where necessary
class Copy a => Share a

-- Special Drop class. A value of a discardable type doesn't have to be used. 
-- Compiler implicitly inserts 'kill' where nceessary
class Kill a => Drop a



Possible mechanics of simple lenses with records (and linearity):

Foo :: Foo b in a => Lens a b

Linear types

copy :: forall a. Share a => a -> (a, a)



Should view take read-only ref, return read-only? 

view :: Lens a b -> a! -> b!

^ What about record that has a mix of linear and non-linear components?
I think it's OK?

over :: Lens a b -> (b -> b) -> a -> a 

set :: Drop b => Lens a b -> b -> a -> a

Is the Drop constraint necessary? Don't think so?

Linear functions: E.g., in the above if we partially apply lens and b, we should only apply function (a -> a) once!


f :: a -> () -> a
f x = () -> x

f x must be linear otherwise we can do
let y = f x in (y (), y ())

But if a is not linear don't want to make f x non-linear 
Linearity of f x has to depend on x...


Actual function type: Workout capture list. If any are linear, function becomes linear. Static dispatch.
f = \x -> (\() -> x)
          ^........
x :: a captured.

f :: a -> () {a}-> a

let y = linear :: a
    f = \x -> \() -> (x, y)
    f :: forall b. b {a,b}-> () {a,b}-> (b, a)
    If ^ at this stage we know a is linear, then
    f :: forall b. b *> () *> (b, a)




Functor f => (b -> f b) -> (a -> f a)





x = { Foo 2 , ... }


let y = 1 + view Foo x 

Can't let (view Foo x) outlive x
Don't want to mix x! and x in same region
let! does this.

let! (y1,...) x = e1 in e2




Effect types + Laziness = Terrible idea.
Effect types + Strict = GOOD idea.

read :: Read a => () -> a # Read

map :: (a -> b) -> [a] -> [b] 
Doesn't take effect types in to account

map :: (a -> b # e) -> [a] -> [b] # e

($) :: (a -> b # e) -> a -> b # e

let x = read () :: Int # Read
in  (here the type of x is just Int)
  ...
  y :: T

:: y # Read


x :: Int # e1
y :: String # e2
(x, y) :: (Int, String) # e1, e2

x :: () -> Int # e1
y :: () -> String # e2
(x, y) :: ( () -> Int # e1, () -> String # e2 )

Need sequence (comma) operator

% abstract type
type Shared a

get :: Shared a -> a # ReadHeap
put :: Shared a -> a -> () # WriteHeap

% smart constructors?
data Thunk (a#e) = Thunk { cache :: Shared (Maybe a), generator :: () -> a#e }

makeThunk :: (() -> a#e) -> Thunk (a#e)
makeThunk f = Thunk { cache = makeShared Nothing, generator = f }

% Should technically be Thunk a -> a # Heap
# axiomatise
get :: Thunk (a#e) -> a#e
get t = case get (cache t) of Nothing -> let x = generator t () in put (cache t) x then x
                              Just x  -> x

but then this clashes with if then else ... (That's OK)
optional else?
if c then e
<==> 
if c then kill e else ()
kill :: a -> ()
or
if c then Just e else Nothing

Are monads still useful? Sure! Maybe, List monads etc.


x, y
x `seq` y
x `then` y
seq {x; y}



(a, b, c)
sugar for
(a, (b, c))
(Since it's strict)

No anonymous records/variants.
Structured ones.


Avoid take etc? Just use lenses!

view :: Lens whole part -> whole -> part
over :: Lens whole part -> (part -> part) -> whole -> whole
set :: Drop part => Lens whole part -> part -> whole -> whole

\x -> kill x then part

Foo.Bar :: Foo.Bar b in a => Lens a b 
Can constraint to Foo.Bar b! in a! => Lens a! b!
view Foo.Bar :: Foo.Bar b in a => a -> b
             :: Foo.Bar b! in a! => a! -> b!

(b -> f b) -> (a -> f a)


Foo :: forall (part :: *) (whole :: *). (Foo part) in whole => Lens whole part

Foo.Bar part in whole =>


bang
(!) :: * -> *

copy :: a! -> a
or
copy :: a -> (a, a) -- This one can be expressed in terms of the other
copy x = let! (x) y = copy x in (x, y)

class Copy a where
  copy :: a! -> a

class Kill a where
  kill :: a -> ()


Share p => p -> (p,p)


(++) :: [a] -> [a] -> [a]
(++) []     ys = ys                <-- Pattern matching 'breaks' xs down. Introduces new variables. Those variables might be linear.
(++) (x:xs) ys = x : (xs ++ ys)

length :: [a]! -> Int


====================================
Foo.Bar a in b <==> Foo.Bar a! in b!
====================================


Allow pattern matching on abstract types?
[] for Vector ?
I think this could be a bad idea..


If Xxxx is lens then how do we construct things?
Perhaps every scope that contains dataconstructor / field name Foo automatically generates lens foo

{ xxx :: T1, yyy :: T2 }
{ Xxx :: T1, Yyy :: T2 }

Variants?
{ xxx :: T1 | yyy :: T2 }
{ Xxx :: T1 | Yyy :: T2 }

Qualification ?



snd :: Lens (a, b) b

snd . snd :: Lens (a, (b, c)) c

Prisms for variants?



copy and kill should be PURE. Then the compiler can implicit insert them where it needs/wants to. E.g., has freedom to pass by value OR const reference for non-linear type.
Maybe copy and kill should be for Share/ Drop? Otherwise we could do copy a = (a, a) for primitive type, but this isn't a valid copy... copy should be inbuilt for non-abstract types.


If we implement take notation, record lenses can be complex. This can be good (more powerful). But might cause confusing error messages.
forall a b c. foo b in a -> Lens a (a take foo b put foo c) b c  



Potetnial problems:
Poly top-level bindings.
Generalised poly bindings.
let
[(n,s)] = ... :: forall a. C a => [(a, String)]
in
...
Can't know how to specialise s :: String?.


For fusion, we should be able to say which side effects interact with what.
e.g.,
interacts ReadIO WriteIO
interacts ReadIO ReadIO

This would allow term rewriting/reordering EVEN for impure code! Awesome!




filter id primes !primes finally kill primes
vs
filter id !primes finally kill primes

filter id !primes 
same as
read primes in filter id primes
?
or
let !primes in filter id primes


 

Note: For polymorphic ffi: All type variables must be determinable at compile time. (Including in return I think..) Then they can be implemented as template functions.
^-- Maybe do this for everything. No rank2 types.

Lens as abstract type (so we can avoid rank2 types)

foo :: a! -> a -> Int
template <typename A_ref, typename A_>
Int foo(A_Ref _, A _) { ... }

A_Ref could be A* or it could just be A
Int is a type alias for int

or maybe (A&& _, A&& _) ?


Multiparam type classes and functional dependencies.
class Copy (a :: Type) (e :: Effect) | a -> e where
      copy :: a! -> a # e

class Copy a Pure => Share a

* as alias for Type
# as alias for Effect?
or # for ImpureType? 


Numeric literals.
4 :: Int by default? 4N :: Num a or 4?

or 4 :: Num a, with type defaulting?
or 4 :: Num a. 4I :: Integer or 4i :: Int 


Pumpkins idea: Might be a good idea to have syntax construct to temporarily un-linearise linear type to avoid lots of dupe's and bindings.
