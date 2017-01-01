{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Metamorph.Internal where

import Control.Applicative
import Data.Coerce
import Data.List (stripPrefix)
import GHC.Exts (Constraint, proxy#)
import GHC.TypeLits
import Test.QuickCheck
import Test.QuickCheck.Gen (Gen(..))
import Unsafe.Coerce

type family ProductCont r (as :: [*]) :: * where
  ProductCont r '[] = r
  ProductCont r (a ': as) = a -> ProductCont r as

-- | Monomial: product of elements.
newtype MonoCont (name :: Symbol) r as = MonoCont (ProductCont r as)

type Product' as = forall r. ProductCont r as

type family SumProduct r (as :: [[*]]) :: * where
  SumProduct r '[] = r
  SumProduct r (a ': as) = ProductCont r a -> SumProduct r as

type SumProduct' as = forall r. SumProduct r as

type family SumMono r (names :: [Symbol]) (as :: [[*]]) :: * where
  SumMono r '[] '[] = r
  SumMono r (aName ': aNames) (a ': as) = MonoCont aName r a -> SumMono r aNames as

newtype SumMono_ r names as = SumMono_ (SumMono r names as)

-- | Polynomial: sum of monomials.
newtype Poly' (name :: Symbol) (aNames :: [Symbol]) as
  = Poly (forall r. SumMono_ r aNames as)

type Poly name as = Poly' name (MapFst as) (MapSnd as)

type family Sum r (as :: [*]) :: * where
  Sum r '[] = r
  Sum r (a ': as) = (a -> r) -> Sum r as

type family Trace a :: *
type instance Trace (a -> b) = Poly "(->)" '[ '("<fun>", '[ a, Trace b ]) ]
type instance Trace () = Poly "()" '[]
type instance Trace (a, b) = Poly "(,)" '[
  '("({_}, _)", '[ Trace a ]),
  '("(_, {_})", '[ Trace b ])]
type instance Trace (Either a b) = Poly "Either" '[
  '("Left {_}", '[ Trace a ]),
  '("Right {_}", '[ Trace b ])]
type instance Trace (Maybe a) = Poly "Maybe" '[ '("Just {_}", '[ Trace a ]) ]
type instance Trace [a] = Poly "[]" '[ '("<list>", '[ Int, Trace a ]) ]

type family MapSnd (as :: [(k1, k2)]) :: [k2] where
  MapSnd '[] = '[]
  MapSnd ('(_, a) ': as) = a ': MapSnd as

type family MapFst (as :: [(k1, k2)]) :: [k1] where
  MapFst '[] = '[]
  MapFst ('(a, _) ': as) = a ': MapFst as

unPoly :: forall r names as name. Poly' name names as -> SumProduct r as
unPoly = unsafeCoerce

mkTrace
  :: forall a name names as
  .  (Trace a ~ Poly' name names as)
  => (forall r. SumProduct r as) -> Trace a
mkTrace = unsafeCoerce

-----------

-- | PROOF that mkTrace is safe.
--
-- Assuming additionally that
-- Coercible (f r) (g r) => Coercible (forall r. f r) (forall r. g r)
mkTraceCheck
  :: forall name names as
  .  (Reify2 names as)
  => (forall r. SumProduct r as) -> Poly' name names as
mkTraceCheck s = Poly (
  (case rr @r @names @as reify2
    :: Coercer (SumProduct r as) (SumMono_ r names as)
  of
    C -> coerce (s @r :: SumProduct r as)
  ) :: forall r. SumMono_ r names as)

data Coercer a b where
  C :: Coercible a b => Coercer a b

rr :: forall r names as. R2 names as -> Coercer (SumProduct r as) (SumMono_ r names as)
rr RN = C
rr (RC reify) = case rr @r reify of
  C -> C

data R2 :: [k1] -> [k2] -> * where
  RN :: R2 '[] '[]
  RC :: R2 xs ys -> R2 (x ': xs) (y ': ys)

class Reify2 (a1 :: [k1]) (a2 :: [k2]) where
  reify2 :: R2 a1 a2

instance Reify2 '[] '[] where
  reify2 = RN

instance Reify2 xs ys => Reify2 (x ': xs) (y ': ys) where
  reify2 = RC reify2

-----------

instance PrettyTrace (Poly' name ns as)
  => Show (Poly' name ns as) where
  showsPrec _n = prettyTrace

class PrettyTrace poly where
  prettyTrace :: poly -> ShowS

instance {-# OVERLAPPABLE #-} PrettyTraceSimple ns as
  => PrettyTrace (Poly' name ns as) where
  prettyTrace poly = prettyTraceSimple @ns @as (unPoly @ShowS poly)

instance (Show a, PrettyTrace trace)
  => PrettyTrace (Poly' "(->)" '["<fun>"] '[ '[ a, trace ] ]) where
  prettyTrace (Poly (SumMono_ poly)) =
    poly (MonoCont (\a trace ->
      showString "(\\" .
      showsPrec 11 a .
      showString " -> " .
      prettyTrace trace .
      showString ")"))

instance PrettyTrace trace
  => PrettyTrace (Poly' "[]" '["<list>"] '[ '[ Int, trace ] ]) where
  prettyTrace (Poly (SumMono_ poly)) =
    poly (MonoCont (\n trace ->
      showString "[" .
      shows n .
      showString "=" .
      prettyTrace trace))

class PrettyTraceSimple ns as where
  prettyTraceSimple :: SumProduct ShowS as -> ShowS

instance PrettyTraceSimple '[] '[] where
  prettyTraceSimple s = s

instance (KnownSymbol name, PrettyTrace a, PrettyTraceSimple names as)
  => PrettyTraceSimple (name ': names) ('[a] ': as) where
  prettyTraceSimple s =
    showString "(" .
    prettyTraceSimple @names @as
      (s (\a -> replace "{_}" (prettyTrace a) rootExpr)) .
    showString ")"
    where
      rootExpr = symbolVal' @name proxy#

replace :: Eq a => [a] -> ([a] -> [a]) -> [a] -> ([a] -> [a])
replace old new [] = id
replace old new as | Just as' <- stripPrefix old as = new . (as' ++)
replace old new (a : as) = (a :) . replace old new as

data ReifiedList :: [k] -> * where
  ReifiedNil :: ReifiedList '[]
  ReifiedCons :: ReifiedList as -> ReifiedList (a ': as)

class Reify (a :: [k]) where
  reify :: ReifiedList a

instance Reify '[] where
  reify = ReifiedNil

instance Reify as => Reify (a ': as) where
  reify = ReifiedCons reify

type family All (c :: k -> Constraint) (as :: [k]) :: Constraint where
  All c '[] = ()
  All c (a ': as) = (c a, All c as)

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
      ap :: a -> Trace b -> Trace (a -> b)
      ap a tb = mkTrace @(a -> b) (\k -> k a tb)

instance Applicative m => Traceable z m () where
  trace _ = pure ()

instance (Applicative m, Traceable z m a, Traceable z m b)
  => Traceable z m (a, b) where
  trace cs = liftA2 (,) (trace (cs . fa)) (trace (cs . fb))
    where
      fa ta = mkTrace @(a, b) (\k _ -> k ta)
      fb tb = mkTrace @(a, b) (\_ k -> k tb)

instance (Select m, Traceable z m a, Traceable z m b)
  => Traceable z m (Either a b) where
  trace cs = Left <$> trace (cs . fa) ? Right <$> trace (cs . fb)
    where
      fa ta = mkTrace @(Either a b) (\k _ -> k ta)
      fb tb = mkTrace @(Either a b) (\_ k -> k tb)

instance (Select m, Traceable z m a)
  => Traceable z m (Maybe a) where
  trace cs = pure Nothing ? Just <$> trace (cs . fa)
    where
      fa ta = mkTrace @(Maybe a) (\k -> k ta)

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
    fa ta = mkTrace @[a] (\k -> k n ta)

data family Retrace r a :: *
newtype instance Retrace r (a -> b) = RFun (Sum r '[ Trace a, Retrace r b ])
newtype instance Retrace r Bool = RBool (Sum r '[])

instance (Show (Trace a), Show (Retrace ShowS b))
  => Show (Retrace ShowS (a -> b)) where
  showsPrec n (RFun f) = showParen (n > funPrec) $ f
    (\ta ->
      showsPrec (funPrec + 1) ta .
      showString " -> _")
    (\rtb ->
      showString "_ -> " .
      showsPrec funPrec rtb)
    where
      funPrec = 0

class CoArbitraryRetrace a where
  car :: Retrace (Gen b -> Gen b) a -> Gen b -> Gen b

instance (CoArbitrary (Trace a), CoArbitraryRetrace b)
  => CoArbitraryRetrace (a -> b) where
  car (RFun f) = f coarbitrary car

instance CoArbitrarySumMono ns as => CoArbitrary (Poly' name ns as) where
  coarbitrary (Poly p_) =
    (let SumMono_ p = p_ @(Gen b -> Gen b)
    in casm @ns @as @b p) :: forall b. Gen b -> Gen b

class CoArbitrarySumMono ns as where
  casm :: SumMono (Gen b -> Gen b) ns as -> Gen b -> Gen b

instance CoArbitrarySumMono '[] '[] where
  casm = id

instance (Rotate a, CoArbitraryProduct a, CoArbitrarySumMono ns as)
  => CoArbitrarySumMono (n ': ns) (a ': as) where
  casm :: forall b. SumMono (Gen b -> Gen b) (n ': ns) (a ': as) -> Gen b -> Gen b
  casm f = casm @ns @as . f . MonoCont . rotate @a $ cap @a @b

class CoArbitraryProduct as where
  cap :: Gen b -> ProductCont (Gen b) as

instance CoArbitraryProduct '[] where
  cap = id

instance (CoArbitrary a, CoArbitraryProduct as)
  => CoArbitraryProduct (a ': as) where
  cap g a = cap @as (coarbitrary a g)

class Rotate as where
  rotate :: (r -> ProductCont r as) -> ProductCont (r -> r) as

instance Rotate '[] where
  rotate = id

instance Rotate as => Rotate (a ': as) where
  rotate g a = rotate @as (flip g a)

type F a = a -> (a -> a) -> a

newtype Z = Z (forall r. Retrace r (F A))

instance Show Z where
  showsPrec n z = showParen (n > appPrec) $
    showString "Z " .
    showsPrecZ z
    where
      appPrec = 10

showsPrecZ :: Z -> ShowS
showsPrecZ (Z rt) =
  showsPrec (appPrec + 1) (rt @ShowS)
  where
    appPrec = 10

newtype A = A Z

instance Show A where
  showsPrec n (A z) = showsPrecZ z

newtype instance Retrace r A = RetraceA (Sum r '[])

instance Show (Retrace ShowS A) where
  showsPrec _ (RetraceA r) = r

instance CoArbitraryRetrace A where
  car (RetraceA f) = f

type instance Trace A = Poly "A" '[ '("", '[]) ]

traceA :: Trace A
traceA = Poly (SumMono_ (\(MonoCont p) -> p))

instance Applicative m => Traceable Z m A where
  trace cs = pure (cs traceA A)

instance PrettyTrace (Poly' "A" '[""] '[ '[] ]) where
  prettyTrace _ = showString "A"

instance CoArbitrary A where
  coarbitrary = coarbitrary @Z . coerce

instance CoArbitrary Z where
  coarbitrary (Z f) = car f

generateA :: (forall a. F a) -> Gen A
generateA f = do
  a0 <- trace @Z @Gen @A (\ta ret -> ret (Z (RFun $ \k _ -> k ta)))
  a1 <- trace @Z @Gen @(A -> A) (\ta1 ret -> ret (Z (RFun $ \_ k -> k (RFun $ \k _ -> k ta1))))
  pure (f a0 a1)

f :: forall a. F a
f a g = g a

main = sample (generateA f)
