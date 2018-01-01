* Basic parser, type checker (in Haskell)

* let expressions. literals.
* if then else
* some inbuilt operators e.g., (+) :: Int -> Int -> Int, (<) :: Int -> Int -> Bool, (==) :: Int -> Int -> Bool
* list (polymorphic). type annotations. monomorphism restriction? Might need this for type classes.
* type (can not be recursive)
* data
* lambda functions w/out patterns.
* add patterns to lambda 
* haskell-style functions
* infix, fixity declarations, where clauses

* Start with interpreter. After parsing, type checking, put in some IR and pass to C++.

* Effect types. 'Pure' effect. # precendence. 
* Basic built-in IO.
? data Foo (a :: *) (e :: Effects) or Foo (a#e :: #) ?

* Type classes. Static dispatch.
* Kill and Copy classes. kill and copy should be pure. (why? If Drop resp Share, compiler inserts kill resp copy implicitly. Don't want them to have side effects in that case)

* Linear types (Perhaps some built-in functions on linear types for the moment, e.g., array?). Note: Think about @ patterns. Think about let! and related.

* Records, Simple lenses, Record literal supertyping. Rank 2 types for lenses.


* Modules. When are top-level terms evaluated? 

* FFI (C++ at first). 
* Rewrite built-in functions (as many as possible) in to this. Get it working with linear values.

* GADTs

* Standard Library. Datatypes, algos.




At some time:
Recursive / mutually recursive let expressions. This can be possible if (0work vs pure etc)
Call this letrec instead of let
