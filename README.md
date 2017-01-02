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

```
> f 0 succ :: Integer
```

    3

From the type of `f` and a single value, you can deduce that `f` just iterates
a function three times:

```haskell
f :: forall a. a -> (a -> a) -> a
f a r = r (r (r a))
```

Any polymorphic function is similarly restrained by its type in the range of
possible behaviors it can have, and we can restrict it further by observing
some of its outputs.

Given a universally quantified type, e.g., `forall a. a -> (a -> a) -> a`,
`metamorph` can craft a type `A` and special inputs to perform a sort of
symbolic evaluation of functions of that type.

Reverse engineer functions
--------------------------

Functions of certain types, such as `forall a. a -> (a -> a) -> a`, are
uniquely determined by the image of a single well chosen input. In that case,
we can guess the definition of a polymorphic function with `prettyMorphing`:

```
prettyMorphing :: (...) => String -> monomorphizedType -> String
prettyMorphing :: String -> (A -> (A -> A) -> A) -> String`

> prettyMorphing "f" (f :: A -> (A -> A) -> A)
```

    "f a b = b (b (b a))"

Random evaluation
-----------------

In other cases, `prettyMorphing` won't type check. You may try to use
`morphingGen` to generate some random inputs. Thanks to QuickCheck, even
functions can be generated!

For any function type `F a` and an associated `A` constructed by `metamorph`:

```haskell
morphingGen :: F A -> Test.QuickCheck.Gen (Domain (F A), Codomain (F A))
```

For example, if `F a = [a] -> [a]`, then `Domain (F A) ~ ([A], ())` and
`Codomain (F A) ~ [A]`.

```
> generate (morphingGen (reverse :: [A] -> [A])) >>= \((a, _), c) ->
>   putStrLn $ "a@" ++ pretty_ a ++ " -> " ++ show c
```

    a@[_,_,_,_] -> [a !! 3,a !! 2,a !! 1,a !! 0]

Some list `a` of length 4 was generated, and this shows that the image of `a` under
`reverse` is indeed its reverse.

We use `pretty_` instead of `show` to display the input list with minimal
noise.

Examples can be found under `test/`.

---

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
-- Everything else (Metamorph, Newtype) belongs to Test.Metamorph.
-- The first incantation is one newtype and a trivial (enough) instance
-- to unwrap it.

newtype A' = A' (F (Metamorph A'))

instance Newtype A' where
  type Old A' = F (Metamorph A')
  unwrap (A' a) = a

-- This is the type at which to instantiate f.
-- It is Show-able.
type A = Metamorph A'

-- Monomorphization!
f_ :: A -> (A -> A) -> A
f_ = f

-- For this type, you only need to look at a single value to deduce everything
-- about f. metamorph implicitly and purely computes an ideal pair (A, A -> A)
-- to be applied to f.
--
-- 'morphingPure' applies these arguments to the function, and returns the
-- result.
--
-- > morphingPure :: F A -> A
--
-- 'prettyMorphing' produces a possible definition of the function.
--
-- > prettyMorphing :: String -> F A -> String
--
main = do
  print (morphingPure f_)            -- b (b (b a))
  putStrLn (prettyMorphing "f" f_)   -- f a b = b (b (b a))
```

Future work
-----------

- Documentation.

- We could also enumerate inputs.
  Even if there may be more than one necessary value to observe,
  there are many cases where they live in a very small space;
  e.g., `forall a. [a] -> [a]`, only one list of each length is necessary
  to identify a function of that type.

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

