-- |
--
-- = Overview
--
-- == Trace
--
-- Given a type @t@, @'Trace' t@ is the sum of all possible ways to obtain a
-- value of type @A@ contained in a value of type @t@.
--
-- - For a function, we must apply it to some argument, and we can then recursively
--   obtain a value from the result.
-- - For a sum of products, we can choose to obtain a value from either field
--   of a given constructor.
--
-- > Trace (b -> t)     = TraceFun b (Trace t)
-- > Trace (u, v)       = TraceFst (Trace u) | TraceSnd (Trace v)
-- > Trace (Either u v) = TraceLeft (Trace u) | TraceRight (Trace v)
-- > Trace ()          -- Empty type, there is no A.
-- > Trace A = TraceA  -- One way of getting an A out of A.
--
-- In the case of sum types such as @Either@, the constructors @TraceLeft@ and
-- @TraceRight@ carry redundant information: a value of type @Either u v@ will
-- already indicate which side of the alternative is in effect.
--
-- == Retrace
--
-- Now consider the whole type @s@ of the function to test, such as:
--
-- > s ~ A -> (A -> A) -> A
--
-- @'Retrace' s@ is the sum of all possible ways to obtain a value of type @A@
-- from all /arguments/ of @s@.
--
-- - The main case is of course function types @s = t -> u@, we can either obtain
--   it from @t@ (in a way described by @Trace t@), or from an argument of @u@,
--   recursively.
--
-- - Retrace r for any "result type" r is empty.
--
-- > Retrace (t -> u) = RetraceArg (Trace t) | RetraceImg (Retrace u)
-- > Retrace A
-- > Retrace Bool
--
-- Actually, parameterized types such as tuples and @Either@ may have a
-- non-empty @Retrace@, in order to also consider arguments of functions
-- contained within other values.
--
-- == Defining A
--
-- Let's consider an example.
--
-- > type F a = ((a, a) -> a) -> Either a a -> a
--
-- @f :: forall a. F a@, expects arguments of types @(a, a) -> a@ and
-- @Either a a@.
-- We generate @g :: (A, A) -> A@ and @h :: Either A A@, whose "leaves" of type
-- @A@ correspond to their own positions. Thus we define @A@ as:
--
-- > newtype A = A (Retrace (F A))
--
-- Let us construct @g@ and @h@. Functions just record the argument they are
-- given.
--
-- > g :: (A, A) -> A
-- > g a2 = A . RetraceArg . TraceFun a2 $ TraceA
--
-- For sum types, we must choose a constructor. Hence generation must happen in
-- some context, e.g., @Gen@ to make random choices, we could also
-- @Enumerate@ them, or even do @IO@.
--
-- > gen_h :: Gen (Either A A)
-- > gen_h = elements
-- >   [ Left  (A . RetraceImg . RetraceArg . TraceLeft  $ TraceA)
-- >   , Right (A . RetraceImg . RetraceArg . TraceRight $ TraceA) ]
--
-- An instance @Traceable z m t@ defines a generator of @t@ which thus fills
-- the leaves of type @A@ with their positions, performing effects in @m@ when
-- necessary. The first argument of @trace@ represents the "path" from some
-- root @z@ to the current position, and is used to form the leaves.
--
-- The 'Morphing' type class wraps up and connects the generators
-- and the monomorphized function @f :: F A@.
--
-- == Implementation notes
--
-- - There is actually one more newtype layer between @A@ and @'Retrace' (F A)@,
--   'Metamorph', so that the user does not need to declare too many
--   instances explicitly.
--
-- - 'Trace' and 'Retrace' are in fact defined as type synonym families, to
--   (re)use generic implementations, parameterized by some type-level
--   annotations.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Metamorph.Internal where

import Control.Applicative
import Data.Functor.Identity
import Data.List (stripPrefix)
import GHC.Exts (Constraint)
import GHC.Stack (HasCallStack)
import GHC.TypeLits
import Test.QuickCheck
import Test.QuickCheck.Gen (Gen(..))

-- * Traces

-- | @'Trace' a@ is the sum of ways to obtain a "leaf" of type @Metamorph b@
-- from values of type @a@.
type family Trace a :: *

-- "Concrete types" like '()', 'Bool', 'Integer' contain no leaves,
-- so they have an empty trace type.
type instance Trace () = Void
type instance Trace Bool = Void
type instance Trace Integer = Void
type instance Trace Int = Void

-- | To get a something out of a function, we must first apply it to some
-- argument.
type instance Trace (a -> b) = TraceFun a (Trace b)

-- | In a product type, leaves can be found either component.
type instance Trace (a, b) =
  TField "fst" (Trace a) :+:
  TField "snd" (Trace b)

-- | In a sum type, we just recurse into whichever alternative we
-- are given.
type instance Trace (Either a b) =
  TField "fromLeft" (Trace a) :+:
  TField "fromRight" (Trace b)
type instance Trace (Maybe a) = TField "fromJust" (Trace a)

-- | An optimized representation for lists.
type instance Trace [a] = TraceList (Trace a)

-- | There is a single trivial way to get a leaf out of itself.
type instance Trace (Metamorph a) = TraceEnd

-- ** Trace components

-- | Trace through a field of some constructor.
newtype TField (n :: Symbol) t = TField t

-- | Trace through a function.
data TraceFun a trace = TraceFun a trace
  deriving (Eq, Ord, Show)

-- | Trace through a list.
data TraceList trace = TraceList Int trace
  deriving (Eq, Ord, Show)

-- | Trace end.
data TraceEnd = TraceEnd
  deriving (Eq, Ord, Show)

-- ** Auxiliary types

-- | A pretty-looking sum.
data a :+: b = L a | R b
  deriving (Eq, Ord, Show)

infixr 4 :+:

-- | Empty type.
data Void

instance Eq Void where (==) = absurd
instance Ord Void where compare = absurd
instance Show Void where show = absurd

-- | Ex falso quodlibet.
absurd :: HasCallStack => Void -> a
absurd _ = error "Void"

-- Arbitrary instances.

instance CoArbitrary Void where
  coarbitrary = absurd

instance (CoArbitrary a, CoArbitrary b)
  => CoArbitrary (a :+: b) where
  coarbitrary (L a) = variant 0 . coarbitrary a
  coarbitrary (R b) = variant 1 . coarbitrary b

instance (CoArbitrary a, CoArbitrary trace)
  => CoArbitrary (TraceFun a trace) where
  coarbitrary (TraceFun a trace) = coarbitrary a . coarbitrary trace

instance CoArbitrary TraceEnd where
  coarbitrary _ = id

-- * Traced values.

-- $traced We generate values @v@ whose leaves of type @Metamorph b@ contain
-- the trace through that value to themselves.

-- | Generate a traced value @a@ in context @m@
-- (e.g., 'Identity', 'Gen', 'IO'), with final trace type @z@.
class Traceable z m a where
  trace :: (Trace a -> z) -> m a

-- Types with no leaf to trace just use default generators.

instance Applicative m => Traceable z m () where
  trace _ = pure ()

instance Traceable z Gen Bool where
  trace _ = arbitrary

instance Traceable z Gen Integer where
  trace _ = arbitrary

instance Traceable z Gen Int where
  trace _ = arbitrary

instance (Splittable m a, Traceable z m b)
  => Traceable z m (a -> b) where
  trace cs = split (\a -> trace (cs . TraceFun a))

instance (Applicative m, Traceable z m a, Traceable z m b)
  => Traceable z m (a, b) where
  trace cs = liftA2 (,) (trace (cs . autotag @"fst")) (trace (cs . autotag @"snd"))

instance (Select m, Traceable z m a, Traceable z m b)
  => Traceable z m (Either a b) where
  trace cs =
    Left <$> trace (cs . autotag @"fromLeft") ?
    Right <$> trace (cs . autotag @"fromRight")

instance (Select m, Traceable z m a)
  => Traceable z m (Maybe a) where
  trace cs = pure Nothing ? Just <$> trace (cs . autotag @"fromJust")

instance (Monad m, Select m, Traceable z m a)
  => Traceable z m [a] where
  trace cs = selectInt >>= \n -> traceList cs n 0

traceList
  :: forall a m z
  .  (Select m, Traceable z m a)
  => (Trace [a] -> z) -> Int -> Int -> m [a]
traceList cs n m | n <= m = pure []
traceList cs n m =
  liftA2 (:)
    (trace (cs . TraceList m))
    (traceList cs n (m + 1))

instance (Applicative m, Newtype a, Retrace (Old a) ~ z)
  => Traceable z m (Metamorph a) where
  trace cs = pure (Metamorph (cs . const TraceEnd))

-- | Contexts with non-deterministic choices.
--
-- This is weaker than 'Alternative' (no 'empty' action).
class Applicative m => Select m where
  -- | Choose between two alternatives.
  (?) :: m a -> m a -> m a
  -- | Choose an integer.
  selectInt :: m Int

infixl 3 ?

instance Select Gen where
  ma ? mb = arbitrary >>= \b -> if b then ma else mb
  selectInt = sized $ \n -> choose (0, n)

-- | Contexts which can commute with @(->) a@.
class Splittable m a where
  split :: (a -> m b) -> m (a -> b)

instance CoArbitrary a => Splittable Gen a where
  split f = MkGen $ \g n a -> unGen (coarbitrary a (f a)) g n

instance Splittable Identity a where
  split f = pure (runIdentity . f)

-- ** Auxiliary type class

-- | Wrap a value in a tagged sum given the corresponding tag.
class Autotag (n1 :: Symbol) a1 as where
  autotag :: a1 -> as

instance Autotag n1 a1 as => Autotag n1 a1 (a :+: as) where
  autotag a = R (autotag @n1 a)

instance {-# OVERLAPPING #-} a1 ~ a => Autotag n1 a1 (TField n1 a :+: as) where
  autotag a = L (TField a)

instance a1 ~ a => Autotag n1 a1 (TField n1 a) where
  autotag = TField

-- * Retrace

-- | We generalize 'Trace' to multiple arguments of a function.
--
-- For a function type @a@, @'Retrace' a@ is the sum of ways to obtain a
-- @'Metamorph' a@ from arguments of @a@.
type Retrace a = Trace (Dual a)

-- | Type of "environments" associated with any type.
--
-- For simple function types, this corresponds to the product of argument
-- types.
--
-- @
-- 'Dual' (a -> b -> c) ~ (a, (b, ()))
-- @
type family Dual a :: *
type instance Dual (a -> b) = (a, Dual b)
type instance Dual (IO a) = ()
type instance Dual (a, b) = a -> Dual b
type instance Dual (Either a b) = Either (Dual a) (Dual b)
type instance Dual (Maybe a) = Maybe (Dual a)
type instance Dual [a] = Maybe (Int, Dual a)
type instance Dual (Metamorph a) = ()
type instance Dual () = ()
type instance Dual Bool = ()
type instance Dual Integer = ()
type instance Dual Int = ()

-- | Values which remember how they were constructed.
--
-- The argument type @a@ of @'Metamorph' a@ must be an instance of 'Newtype'.
newtype Metamorph a = Metamorph (() -> Retrace (Old a))

-- $trace-sharing The definition of 'Metamorph' as a constant function is a
-- trick to improve sharing.

instance (Newtype a, CoArbitrary (Retrace (Old a)))
  => CoArbitrary (Metamorph a) where
  coarbitrary (Metamorph a) = coarbitrary (a ())

-- * Evaluation

-- | Function result type.
--
-- @
-- 'Codomain' (a -> b -> c) ~ c
-- @
type family Codomain a :: *
type instance Codomain (a -> b) = Codomain b
type instance Codomain () = ()
type instance Codomain Bool = Bool
type instance Codomain Integer = Integer
type instance Codomain Int = Int
type instance Codomain (a, b) = (a, b)
type instance Codomain (Either a b) = Either a b
type instance Codomain (Maybe a) = Maybe a
type instance Codomain [a] = [a]
type instance Codomain (Metamorph a) = Metamorph a

-- | Function argument types.
--
-- @
-- 'Domain' (a -> b -> c) ~ (a, (b, ()))
-- @
type family Domain a :: *
type instance Domain (a -> b) = (a, Domain b)
type instance Domain (IO a) = ()
type instance Domain () = ()
type instance Domain Bool = ()
type instance Domain Integer = ()
type instance Domain Int = ()
type instance Domain (a, b) = ()
type instance Domain (Either a b) = ()
type instance Domain (Maybe a) = ()
type instance Domain [a] = ()
type instance Domain (Metamorph a) = ()

-- | Generate traced arguments in context @m@,
-- and apply the given function @a@ to them.
class Applicative m => Morphing z m a where
  morphing' :: (Retrace a -> z) -> a -> m (Domain a, Codomain a)

instance (Monad m, Traceable z m a, Morphing z m b)
  => Morphing z m (a -> b) where
  morphing' k f = do
    a <- trace @z @m @a (k . L . TField)
    (args, r) <- morphing' (k . R . TField) (f a)
    pure ((a, args), r)

pure' :: Applicative m => t -> a -> m ((), a)
pure' _ a = pure ((), a)

instance Applicative m => Morphing z m () where
  morphing' = pure'

instance Applicative m => Morphing z m Bool where
  morphing' = pure'

instance Applicative m => Morphing z m Integer where
  morphing' = pure'

instance Applicative m => Morphing z m Int where
  morphing' = pure'

instance Applicative m => Morphing z m (a, b) where
  morphing' = pure'

instance Applicative m => Morphing z m (Either a b) where
  morphing' = pure'

instance Applicative m => Morphing z m (Maybe a) where
  morphing' = pure'

instance Applicative m => Morphing z m [c] where
  morphing' = pure'

instance Applicative m => Morphing z m (Metamorph a) where
  morphing' = pure'

-- | Evaluate a monomorphized function of type @e@ symbolically,
-- generated in a compatible applicative context @m@.
--
-- If the function type is @forall a. F a@, you most likely want
-- @e ~ F ('Metamorph' A')@.
morphing :: Morphing (Retrace e) m e => e -> m (Domain e, Codomain e)
morphing = morphing' id

-- | When a single evaluation is sufficient, @morphing@ may happen in
-- @Identity@.
morphingPure :: Morphing (Retrace e) Identity e => e -> Codomain e
morphingPure = snd . runIdentity . morphing

-- | In general, inputs may be generated randomly.
--
-- For example, if @f :: forall a. [a] -> [a]@, the length of the input is a
-- dimension to be generated, as @f@ may behave differently depending on it.
morphingGen :: Morphing (Retrace e) Gen e => e -> Gen (Domain e, Codomain e)
morphingGen = morphing

-- | A type class for unwrapping @newtype@ values.
--
-- @
-- newtype N = N t
--
-- instance 'Newtype' N where
--   type 'Old' N = t
--   'unwrap' (N t) = t
-- @
--
-- Forgetting to implement this seems to make the compiler hang for whatever
-- reason.
--
class Newtype n where
  -- | Wrapped type.
  type Old n :: *
  -- | Look inside a @newtype@.
  unwrap :: n -> Old n

