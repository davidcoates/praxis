# Praxis

A strict functional language with effect annotations and linear types.


#### Effect annotations
##### Basics

Separating pure and impure code is a highly useful features of pure functional languages. Haskell uses monads like State and IO to model effectful computations. Praxis, on the other hand, uses effect annotations to mark which computations are pure and which are impure. Just as every term has a type, every term also has an effect annotation. This is a set of all possible effects that could occur when the term is evaluated. For example, if we read from stdin when computing a string `x`, then we would write the annotated type of `x` as
```
x :: String # ReadIO 
```
The type of `x` is still `String`, and so we can pass it to any function that expects a `String`. This makes it easy to mix pure and impure code.
```
words :: String -> [String]

let y = words x
```
Importantly, the effect annotations of the arguments of a function will be added to the output. This ensures that we always have a complete record of possible side effects. In the above snippet, in order to evaluate `y` we have to evaluate `x`. Since evaluating `x` has side effect `ReadIO`, evaluating `y` should also have side effect `ReadIO`.
```
y :: [String] # ReadIO
```

So, although we can mix pure and impure code, we will always have a record of what side effects could have occured.

##### Impure functions

Let's look at a real impure function, `getLine`.
```
getLine :: () -> (String # ReadIO)
```
The annotated type says that `getLine` takes a single unit argument, and returns a `String` with side effect `ReadIO`.

Why the need for the argument `()`? Top-level bindings are evaluated when the module is loaded, since Praxis is static. If we instead had `getLine :: String # ReadIO`, then `getLine` would read a line when the module loads. Subsequent calls to `getLine` would simply return the original value read. This is not what we want! Instead, we want to read a line multiple times. To achieve this, we write `getLine` as a function with a unit argument so that every call `getLine ()` reads a line from stdin. This can be seen from the type signature; `() -> (String # ReadIO)` has no effect annotations at the top-level, indicating it is pure. However, when we call `getLine ()`, the return type is `String # ReadIO` which does have a side effect.


Note that `#` binds tighter than `->`, so we can write the signature without parentheses:
```
getLine :: () -> String # ReadIO
```

##### Multiple side effects

Terms can have multiple side effects, which are written as a comma-separated list (although the order is unimportant).
```
x :: () -> () # ReadIO, WriteIO
x = putString . getLine
