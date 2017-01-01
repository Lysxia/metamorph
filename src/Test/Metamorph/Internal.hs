{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Test.Metamorph.Internal where

import Control.Applicative
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
type instance Trace (a, b) = TraceSimple "(,)" '[
  '("fst", Trace a),
  '("snd", Trace b)]
type instance Trace (Either a b) = TraceSimple "Either" '[
  '("fromLeft", Trace a),
  '("fromRight", Trace b)]
type instance Trace (Maybe a) = TraceSimple "Maybe" '[ '("fromJust", Trace a) ]
type instance Trace [a] = TraceList (Trace a)

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

-- trace<b> (unCons (...))
instance (KnownSymbol n, PrettyTrace a, PrettySum as)
  => PrettySum ('(n, a) ': as) where
  prettySum (TagPlus f) = prettySum . f $ \ta s ->
    prettyTrace ta . showParen True $
      showString (symbolVal' @n proxy#) . showString " " . s

-- trace<b> ((...) a)
instance (Show a, PrettyTrace trace)
  => PrettyTrace (TraceFun a trace) where
  prettyTrace (TraceFun f) = f $ \a tb s ->
    prettyTrace tb . showParen True $
      s .
      showString " " .
      shows a

-- trace<a> ((...) !! n)
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

-- | @Traceable@ implementation for the monomorphic type(s) associated with
-- a type function @F@.
--
-- @
-- newtype A = A (Retrace (F A))
--
-- type instance Trace A = TraceEnd
--
-- instance Applicative m => Traceable (Retrace (F A)) m A where
--   trace = traceEnd A
-- @
traceEnd
  :: (Applicative m, Trace a ~ TraceEnd)
  => (z -> a) -> (forall r. Trace a -> (z -> a) -> a) -> m a
traceEnd wrap cs = pure (cs TraceEnd wrap)

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

data family Retrace a :: *
newtype instance Retrace (a -> b) = RFun (forall r. Sum r '[ Trace a, Retrace b ])
newtype instance Retrace Bool = RBool (forall r. Sum r '[])

class PrettyRetrace t where
  prettyRetrace :: Retrace t -> (ShowS -> ShowS) -> ShowS

instance (PrettyTrace (Trace a), PrettyRetrace b)
  => PrettyRetrace (a -> b) where
  prettyRetrace (RFun f) = f
    (\ta cxt ->
      prettyTrace ta $
        showParen True (cxt (showString "* -> _")))
    (\rtb cxt ->
      prettyRetrace rtb (cxt . (showString "_ -> " .)))
    where
      funPrec = 0

instance PrettyRetrace a => Show (Retrace a) where
  showsPrec _ a = prettyRetrace a id

class CoArbitraryRetrace a where
  car :: Retrace a -> Gen b -> Gen b

instance (CoArbitrary (Trace a), CoArbitraryRetrace b)
  => CoArbitraryRetrace (a -> b) where
  car (RFun f) = f coarbitrary car

instance CoArbitraryRetrace Bool where
  car (RBool r) = r

