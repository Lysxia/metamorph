Test Polymorphic Functions with Metamorph
=========================================

I give you an unknown function:

```haskell
f :: forall a. a -> (a -> a) -> a
```

By looking at its type, you know it can do only one thing: iterate the second
argument on the first one a fixed number of times. You can easily extract that
number out of the function by instantiating `f` at the type of integers, and
by applying it to `0` and `succ`.

    > f 0 succ :: Integer
    3

From the type of `f` and a single value, you can deduce that `f` just iterates
a function three times:

```haskell
f :: a -> (a -> a) -> a
f a r = r (r (r a))
```

Any polymorphic function is similarly restrained by its type in the range of
possible behaviors it can have, and we can restrict it further by observing
some of its outputs.

Given a universally quantified type, e.g., `forall a. a -> (a -> a) -> a`,
`metamorph` can craft a type `A` and special inputs to perform a sort of
symbolic evaluation of functions of that type.

These inputs are computed by `runtrace`, which simply returns the result.

```haskell
runtrace :: (A -> (A -> A) -> A) -> Identity A
```

We can print it.

    > print (runIdentity (runtrace (f :: A -> (A -> A) -> A)))
    ([_ -> * -> _] ([_ -> * -> _] ([_ -> * -> _] [* -> _])))

Meaning:

    a = [* -> _]
    r = [_ -> * -> _]

    f a r = r (r (r a))

---

Examples can be found under `test/`.

```haskell
-- No Template Haskell! Magic!

{-# LANGUAGE TypeFamilies #-}

import Data.Functor.Identity
import Test.Metamorph

type F a = a -> (a -> a) -> a

-- This is our polymorphic function.
f :: {- forall a. -} F a
f a r = r (r (r a))

-- The only ingredient you need to invent is the type synonym F.
-- Everything else (Retrace, Newtype) belongs to Test.Metamorph.
-- The first incantation is one newtype and a trivial (enough) instance
-- to unwrap it.

newtype A' = A' (F (Retrace A'))

instance Newtype A' where
  type Old A' = F (Retrace A')
  unwrap (A' a) = a

-- This is the type at which to instantiate f.
-- It is Show-able.
type A = Retrace A'

-- Monomorphization!
f_ :: A -> (A -> A) -> A
f_ = f

-- The second incantation is runtrace. It takes the monomorphized function,
-- generates some magical arguments to be applied to and returns the result.
-- For this type, you only need to look at a single value to deduce everything
-- about f, and runtrace holds an ideal pair (A, (A -> A)) that it can
-- produce purely (to be applied to f)!
--
-- > runtrace :: (A -> (A -> A) -> A) -> Identity A

main = print (runIdentity (runtrace f_))
```

`runtrace` can execute in `Identity` precisely when the function can entirely
be determined by a single well chosen input.
In other cases, using `Identity` will just not typecheck.

Instead, you may try generating some random inputs thanks to QuickCheck;
even functions can be generated!

```haskell
runtrace :: F A -> Test.QuickCheck.Gen A
```

Future work
-----------

- Actual documentation. Also, better names.

- We could also enumerate inputs.
  Even if there may be more than one necessary value to observe,
  there are many cases where they live in a very small space;
  e.g., `forall a. [a] -> [a]`, only one list of each length is necessary
  to characterise a function of that type.

- Generic implementation for algebraic data types.
  The type `F` must currently use only:

  - `()`, `Bool`, `Integer`, `Int`,
    `(->)`, `(,)`, `Either`, `Maybe`, `[]`.

P.S.
----

If you have two or more type parameters:

```haskell
type G2 a b = (a -> b -> b) -> [a] -> b -> b
```

Merging them will do the right thing:

```haskell
type G a = G2 a a
```

Reference
=========

- [*Testing polymorphic properties.*](http://publications.lib.chalmers.se/records/fulltext/local_99387.pdf)
  Jean-Philippe Bernardy, Patrik Jansson, and Koen Claessen. 2010.  
  In Proceedings of the 19th European conference on
  Programming Languages and Systems (ESOP'10), Andrew D. Gordon (Ed.).
  Springer-Verlag, Berlin, Heidelberg, 125-144.

The main idea comes from this paper: we can construct a "good" type to test
polymorphic functions on. The given construction is decomposed into simple
operations on types, which works well for proofs, but that seems tough to
implement in Haskell.

`metamorph` takes a more streamlined approach centered on the notion of
symbolic evaluation. Interestingly, it turns out that GHC's type families
suffice to implement this without using Template Haskell.

