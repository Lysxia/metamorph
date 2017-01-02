{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
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
import GHC.Exts (Constraint, proxy#)
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

-- * Showing traces.

class PrettyTrace t where
  prettyTrace :: t -> ShowS -> ShowS

class PrettySum as where
  prettySum :: Sum' (ShowS -> ShowS) as -> ShowS -> ShowS

instance PrettySum as
  => PrettyTrace (TraceSimple n0 as) where
  prettyTrace (TraceSimple t) = prettySum t

instance PrettySum '[] where
  prettySum (TagEmpty s) = s

-- <trace> (unCons (...))
instance (KnownSymbol n, PrettyTrace a, PrettySum as)
  => PrettySum ('(n, a) ': as) where
  prettySum (TagPlus f) = prettySum . f $ \ta s ->
    prettyTrace ta . showParen True $
      showString (symbolVal' @n proxy#) . showString " " . s

-- <trace> ((...) a)
instance (Show a, PrettyTrace trace)
  => PrettyTrace (TraceFun a trace) where
  prettyTrace (TraceFun f) = f $ \a tb s ->
    prettyTrace tb . showParen True $
      s .
      showString " " .
      showsPrec 11 a

-- <trace> ((...) !! n)
instance PrettyTrace trace
  => PrettyTrace (TraceList trace) where
  prettyTrace (TraceList f) = f $ \n ta s ->
    prettyTrace ta . showParen True $
      s .
      showString " !! " .
      shows n

instance PrettyTrace TraceEnd where
  prettyTrace _ = id

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
  trace :: (forall r. Trace a -> (z -> r) -> r) -> m a

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
  => Int -> (forall r. Trace [a] -> (z -> r) -> r) -> m [a]
traceList n cs =
  pure [] ?
  liftA2 (:) (trace (cs . fa)) (traceList (n + 1) cs)
  where
    fa ta = TraceList $ \k -> k n ta

instance (Applicative m, Newtype a, Retrace (Old a) ~ z)
  => Traceable z m (Metamorph a) where
  trace cs = pure (cs TraceEnd Metamorph)

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

newtype RetraceFun trace retrace = RetraceFun (forall r. Sum r '[ trace, retrace ])
newtype Void = Void (forall r. r)

type family Retrace a :: *
type instance Retrace (a -> b) = RetraceFun (Trace a) (Retrace b)
type instance Retrace () = Void
type instance Retrace Bool = Void
type instance Retrace Integer = Void
type instance Retrace Int = Void
type instance Retrace (_, _) = Void
type instance Retrace (Either _ _) = Void
type instance Retrace (Maybe _) = Void
type instance Retrace [c] = Void
type instance Retrace (Metamorph a) = Void

-- | A type of values which remember how they were constructed.
--
-- The argument @a@ of @'Metamorph' a@ must be an instance of 'Newtype'.
newtype Metamorph a = Metamorph (Retrace (Old a))

class PrettyRetrace t where
  prettyRetrace :: t -> (ShowS -> ShowS) -> ShowS

instance (PrettyTrace trace, PrettyRetrace retrace)
  => PrettyRetrace (RetraceFun trace retrace) where
  prettyRetrace (RetraceFun f) = f
    (\t cxt ->
      prettyTrace t $
        showBkt (cxt (showString "* -> _")))
    (\rt cxt ->
      prettyRetrace rt (cxt . (showString "_ -> " .)))
    where
      showBkt s = showString "[" . s . showString "]"

instance PrettyRetrace Void where
  prettyRetrace (Void f) = f

instance (Newtype a, PrettyRetrace (Retrace (Old a)))
  => Show (Metamorph a) where
  showsPrec _ (Metamorph a) = prettyRetrace a id

instance (PrettyTrace trace, PrettyRetrace retrace)
  => Show (RetraceFun trace retrace) where
  showsPrec _ a = prettyRetrace a id

instance (CoArbitrary trace, CoArbitrary retrace)
  => CoArbitrary (RetraceFun trace retrace) where
  coarbitrary (RetraceFun f) = f coarbitrary coarbitrary

instance CoArbitrary Void where
  coarbitrary (Void r) = r

instance (Newtype a, CoArbitrary (Retrace (Old a)))
  => CoArbitrary (Metamorph a) where
  coarbitrary (Metamorph a) = coarbitrary a

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
type instance Untrace [a] = [a]  -- Could be more general.
type instance Untrace (Metamorph a) = Metamorph a

class Applicative m => Morphing z m a where
  morphing' :: (Retrace a -> z) -> a -> m (Untrace a)

instance (Monad m, Traceable z m a, Morphing z m b)
  => Morphing z m (a -> b) where
  morphing' k f = do
    a <- trace @z @m @a (\ta ret -> ret (k (RetraceFun $ \k _ -> k ta)))
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
  morphing' _ a = pure a

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

