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
import GHC.TypeLits
import Test.QuickCheck
import Test.QuickCheck.Gen (Gen(..))

import Test.Metamorph.Generic

newtype TraceSimple (n0 :: Symbol) (as :: [(Symbol, *)])
  = TraceSimple (forall r. Sum' r as)

newtype TraceFun a trace
  = TraceFun (forall r. ProductCont r '[ a, trace ] -> r)

newtype TraceList trace
  = TraceList (forall r. ProductCont r '[ Int, trace ] -> r)

data TraceEnd = TraceEnd
  deriving (Eq, Ord, Show)

type family Trace a :: *
type instance Trace (a -> b) = TraceFun a (Trace b)
type instance Trace () = TraceSimple "()" '[]
type instance Trace Bool = TraceSimple "Bool" '[]
type instance Trace Integer = TraceSimple "Integer" '[]
type instance Trace Int = TraceSimple "Int" '[]
type instance Trace (a, b) = TraceSimple "(,)" '[
  '("fst", Trace a),
  '("snd", Trace b)]
type instance Trace (Either a b) = TraceSimple "Either" '[
  '("fromLeft", Trace a),
  '("fromRight", Trace b)]
type instance Trace (Maybe a) = TraceSimple "Maybe" '[ '("fromJust", Trace a) ]
type instance Trace [a] = TraceList (Trace a)
type instance Trace (Metamorph a) = TraceEnd

-- * Generating values.

class Applicative m => Select m where
  (?) :: m a -> m a -> m a
  select :: [m a] -> m a

class Splittable m a where
  split :: (a -> m b) -> m (a -> b)

infixl 3 ?

instance CoArbitrary a => Splittable Gen a where
  split f = MkGen $ \g n a -> unGen (coarbitrary a (f a)) g n

instance Splittable Identity a where
  split f = pure (runIdentity . f)

instance Select Gen where
  ma ? mb = arbitrary >>= \b -> if b then ma else mb
  select = oneof

class Traceable z m a where
  trace :: (Trace a -> z) -> m a

instance (Splittable m a, Traceable z m b)
  => Traceable z m (a -> b) where
  trace cs = split (\a -> trace (cs . ap a))
    where
      ap a tb = TraceFun (\k -> k a tb)

instance Applicative m => Traceable z m () where
  trace _ = pure ()

instance Traceable z Gen Bool where
  trace _ = arbitrary

instance Traceable z Gen Integer where
  trace _ = arbitrary

instance Traceable z Gen Int where
  trace _ = arbitrary

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

instance (Select m, Traceable z m a)
  => Traceable z m [a] where
  trace = traceList 0

traceList
  :: forall a m z
  .  (Select m, Traceable z m a)
  => Int -> (Trace [a] -> z) -> m [a]
traceList n cs =
  pure [] ?
  liftA2 (:) (trace (cs . fa)) (traceList (n + 1) cs)
  where
    fa ta = TraceList $ \k -> k n ta

instance (Applicative m, Newtype a, Retrace (Old a) ~ z)
  => Traceable z m (Metamorph a) where
  trace cs = pure (Metamorph (cs . const TraceEnd))

autotag :: forall n1 a1 n0 as. Autotag n1 a1 as => a1 -> TraceSimple n0 as
autotag a = TraceSimple (autotag' @n1 a)

class TagReturn as where
  tagReturn' :: r -> Sum' r as

instance TagReturn '[] where
  tagReturn' = TagEmpty

instance TagReturn as => TagReturn ('(n, a) ': as) where
  tagReturn' = TagPlus . const . tagReturn'

class Autotag (n1 :: Symbol) a1 as where
  autotag' :: a1 -> Sum' r as

instance Autotag n1 a1 as => Autotag n1 a1 ('(n, a) ': as) where
  autotag' a = TagPlus $ \_ -> autotag' @n1 a

instance {-# OVERLAPPING #-} (TagReturn as, a1 ~ a) => Autotag n1 a1 ('(n1, a) ': as) where
  autotag' a = TagPlus $ \k -> tagReturn' (k a)

-- * Coarbitrary

instance CoArbitrarySum as => CoArbitrary (TraceSimple name as) where
  coarbitrary (TraceSimple f) = coarbitrarySum 0 f

class CoArbitrarySum as where
  coarbitrarySum :: Int -> Sum' (Gen b -> Gen b) as -> Gen b -> Gen b

instance CoArbitrarySum '[] where
  coarbitrarySum _ (TagEmpty vary) = vary

instance (CoArbitrary a, CoArbitrarySum as)
  => CoArbitrarySum ('(n, a) ': as) where
  coarbitrarySum n (TagPlus f) =
    coarbitrarySum (n + 1)
      (f (\a -> variant n . coarbitrary a))

instance (CoArbitrary a, CoArbitrary trace)
  => CoArbitrary (TraceFun a trace) where
  coarbitrary (TraceFun f) = f . cap @'[a, trace]

class CoArbitraryProduct as where
  cap :: Gen b -> ProductCont (Gen b) as

instance CoArbitraryProduct '[] where
  cap = id

instance (CoArbitrary a, CoArbitraryProduct as)
  => CoArbitraryProduct (a ': as) where
  cap g a = cap @as (coarbitrary a g)

instance CoArbitrary TraceEnd where
  coarbitrary _ = id

-- * Retrace

newtype RetraceSimple (n0 :: Symbol) (as :: [(Symbol, *)])
  = RetraceSimple (forall r. Sum' r as)

type Void (n0 :: Symbol) = RetraceSimple n0 '[]

newtype RetraceFun trace retrace
  = RetraceFun (forall r. Sum r '[ trace, retrace ])

newtype RetraceList retrace
  = RetraceList (forall r. ProductCont r '[ Int, retrace ] -> r)

type family Retrace a :: *
type instance Retrace (a -> b) = RetraceFun (Trace a) (Retrace b)
type instance Retrace () = Void "()"
type instance Retrace Bool = Void "Bool"
type instance Retrace Integer = Void "Integer"
type instance Retrace Int = Void "Int"
type instance Retrace (a, b) = RetraceSimple "(,)" '[
  '("(*, _)", Retrace a),
  '("(_, *)", Retrace b)]
type instance Retrace (Either a b) = RetraceSimple "Either" '[
  '("Either * _", Retrace a),
  '("Either _ *", Retrace b)]
type instance Retrace (Maybe a) = RetraceSimple "Maybe" '[
  '("Maybe *", Retrace a)]
type instance Retrace [a] = RetraceList (Retrace a)
type instance Retrace (Metamorph a) = Void "Metamorph _"

-- | A type of values which remember how they were constructed.
--
-- The argument @a@ of @'Metamorph' a@ must be an instance of 'Newtype'.

-- The definition as a constant function is a trick to improve sharing.
newtype Metamorph a = Metamorph (() -> Retrace (Old a))

instance (CoArbitrary trace, CoArbitrary retrace)
  => CoArbitrary (RetraceFun trace retrace) where
  coarbitrary (RetraceFun f) = f coarbitrary coarbitrary

instance CoArbitrarySum as => CoArbitrary (RetraceSimple n0 as) where
  coarbitrary (RetraceSimple r) = coarbitrarySum 0 r

instance (Newtype a, CoArbitrary (Retrace (Old a)))
  => CoArbitrary (Metamorph a) where
  coarbitrary (Metamorph a) = coarbitrary (a ())

-- * Untrace

type family Untrace a :: *
type instance Untrace (a -> b) = Untrace b
type instance Untrace () = ()
type instance Untrace Bool = Bool
type instance Untrace Integer = Integer
type instance Untrace Int = Int
type instance Untrace (a, b) = (a, b)
type instance Untrace (Either a b) = Either a b
type instance Untrace (Maybe a) = Maybe a
type instance Untrace [a] = [a]
type instance Untrace (Metamorph a) = Metamorph a

class Applicative m => Morphing z m a where
  morphing' :: (Retrace a -> z) -> a -> m (Untrace a)

instance (Monad m, Traceable z m a, Morphing z m b)
  => Morphing z m (a -> b) where
  morphing' k f = do
    a <- trace @z @m @a (\ta -> k (RetraceFun $ \k _ -> k ta))
    morphing' (k . \rtb -> RetraceFun $ \_ k -> k rtb) (f a)

instance Applicative m => Morphing z m () where
  morphing' _ = pure

instance Applicative m => Morphing z m Bool where
  morphing' _ = pure

instance Applicative m => Morphing z m Integer where
  morphing' _ = pure

instance Applicative m => Morphing z m Int where
  morphing' _ = pure

instance Applicative m => Morphing z m (a, b) where
  morphing' _ = pure

instance Applicative m => Morphing z m (Either a b) where
  morphing' _ = pure

instance Applicative m => Morphing z m (Maybe a) where
  morphing' _ = pure

instance Applicative m => Morphing z m [c] where
  morphing' _ = pure

instance Applicative m => Morphing z m (Metamorph a) where
  morphing' _ = pure

-- | Evaluate a monomorphized function of type @e@ symbolically,
-- generated in a compatible applicative context @m@.
--
-- If the function type is @forall a. F a@, you most likely want
-- @e ~ F ('Metamorph' A')@.
morphing :: Morphing (Retrace e) m e => e -> m (Untrace e)
morphing = morphing' id

-- | When a single evaluation is sufficient, @morphing@ may happen in
-- @Identity@.
morphingPure :: Morphing (Retrace e) Identity e => e -> Untrace e
morphingPure = runIdentity . morphing

-- | In general, inputs may be generated randomly.
--
-- For example, if @f :: forall a. [a] -> [a]@, the length of the input is a
-- dimension to be generated, as @f@ may behave differently depending on it.
morphingGen :: Morphing (Retrace e) Gen e => e -> Gen (Untrace e)
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

