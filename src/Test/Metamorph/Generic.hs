{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Metamorph.Generic where

import Control.Applicative (liftA2)
import Data.Proxy (Proxy(..))
import GHC.Exts (proxy#, TYPE)
import GHC.Generics
import GHC.TypeLits
import Test.QuickCheck

import Test.Metamorph.Internal hiding ((:+:))
import Test.Metamorph.Pretty
import qualified Test.Metamorph.Internal as Metamorph

genericTrace
  :: forall a m z w proxy
  .  ( Functor m
     , Generic a
     , GTraceable w z m (Rep a)
     , TraceOf a ~ GTraceOf (Rep a) )
  => proxy '(a, w) -> (Trace a -> z) -> m a
genericTrace _ cs = to <$> gtrace @w (cs . Trace)

weights :: forall ns a. Generic a => Proxy '(a, WeightTree (Rep a) ns)
weights = Proxy

weights' :: forall ns a. Generic a => Proxy '(a, WeightTree' (Rep a) ns)
weights' = Proxy

uniform :: Generic a => Proxy '(a, UniformTree (Rep a))
uniform = Proxy

newtype GTField (n :: Symbol) (i :: Nat) (j :: Nat) a = GTField a

type family GTraceOf (f :: * -> *) :: * where
  GTraceOf V1 = Void
  GTraceOf (f :+: g) = GTraceOf f Metamorph.:+: GTraceOf g
  GTraceOf (S1 _ f) = GTraceOf f
  GTraceOf (C1 ('MetaCons c _ _) f) =
    GTraceProd c 1 (GProdLength f) f
  GTraceOf (D1 _ f) = GTraceOf f

type family GTraceProd
  (n :: Symbol)
  (i :: Nat)
  (j :: Nat)
  (f :: * -> *) :: *
  where
  GTraceProd n i j (f :*: g) =
    GTraceProd n i j f Metamorph.:+:
    GTraceProd n (i + GProdLength f) j g
  GTraceProd n i j (M1 _ _ f) = GTraceProd n i j f
  GTraceProd n i j U1 = Void
  GTraceProd n i j (K1 _ a) = GTField n i j (Trace a)

type family GSumLength (f :: * -> *) :: Nat where
  GSumLength (f :+: g) =
    GSumLength f + GSumLength g
  GSumLength (M1 _ _ _) = 1

type family GProdLength (f :: * -> *) :: Nat where
  GProdLength (f :*: g) =
    GProdLength f + GProdLength g
  GProdLength (M1 _ _ f) = GProdLength f
  GProdLength U1 = 0
  GProdLength (K1 _ _) = 1

type WeightTree (f :: * -> *) (ls :: [*]) = TreeFst (WeightTree0 f ls)
type WeightTree' (f :: * -> *) (ns :: [Nat]) = TreeFst (WeightTree0 f (Map N ns))

type family Map (f :: k1 -> k2) (ns :: [k1]) :: [k2] where
  Map f '[] = '[]
  Map f (n ': ns) = f n ': Map f ns

type family TreeFst (tr :: (*, Nat, [*])) :: (*, Nat) where
  TreeFst '(t, n, '[]) = '(t, n)

type family WeightTree0 (f :: * -> *) (ls :: [*]) :: (*, Nat, [*]) where
  WeightTree0 (f :+: g) ls = WeightTreeCont (WeightTree0 f ls) g
  WeightTree0 (M1 C ('MetaCons c _ _) f) (l ': ls) = '(WLeaf c, Weight c l, ls)
  WeightTree0 (M1 D _ f) ls = WeightTree0 f ls
  WeightTree0 (M1 S _ f) ls = WeightTree0 f ls

type family Weight (c :: Symbol) (l :: *) where
  Weight c (n :%: c) = n
  Weight _ (N n) = n

type family WeightTreeCont (tr :: (*, Nat, [*])) (f :: * -> *) :: (*, Nat, [*]) where
  WeightTreeCont '(t, n, r) g = WeightTreeCont2 t n (WeightTree0 g r)

type family WeightTreeCont2 (t :: *) (n :: Nat) (tr :: (*, Nat, [*])) :: (*, Nat, [*]) where
  WeightTreeCont2 a n '(b, m, r) = '((a :|: b) n, n + m, r)

data (n :: Nat) :%: (c :: Symbol)
data WLeaf (c :: Symbol)
data N (n :: Nat)
data (a :|: b) (n :: Nat)

type family UniformTree (f :: * -> *) :: (*, Nat) where
  UniformTree (f :+: g) = UniformTreeCont (UniformTree f) (UniformTree g)
  UniformTree (M1 C ('MetaCons c _ _) f) = '(WLeaf c, 1)
  UniformTree (M1 D _ f) = UniformTree f
  UniformTree (M1 S _ f) = UniformTree f

type family UniformTreeCont (am :: (*, Nat)) (bn :: (*, Nat)) :: (*, Nat) where
  UniformTreeCont '(a, m) '(b, n) = '((a :|: b) m, m + n)

class GTraceable (w :: (*, Nat)) z m f where
  gtrace :: (GTraceOf f -> z) -> m (f p)

instance Applicative m => GTraceable w z m U1 where
  gtrace _ = pure U1

instance (Functor m, GTraceable w z m f) => GTraceable w z m (M1 D c f) where
  gtrace cs = M1 <$> gtrace @w cs

instance (Functor m, GTraceable w z m f) => GTraceable w z m (M1 S c f) where
  gtrace cs = M1 <$> gtrace @w cs

instance (j ~ GProdLength f, c ~ c', Functor m, GTraceableProd c 1 j z m f)
  => GTraceable '(WLeaf c', _n) z m (M1 C ('MetaCons c _i _s) f) where
  gtrace cs = M1 <$> gtraceprod @c @1 @j cs

instance (KnownNat n, GTraceableSum w z Gen (f :+: g))
  => GTraceable '(w, n) z Gen (f :+: g) where
  gtrace cs = choose (1, n) >>= gtracesum @w cs
    where
      n = fromInteger (natVal' @n proxy#)

class GTraceableSum w z m f where
  gtracesum :: (GTraceOf f -> z) -> Int -> m (f p)

instance
  (KnownNat k, Functor m, GTraceableSum a z m f, GTraceableSum b z m g)
  => GTraceableSum ((a :|: b) k) z m (f :+: g) where
  gtracesum cs n
    | n <= k = L1 <$> gtracesum @a (cs . Metamorph.L) n
    | otherwise = R1 <$> gtracesum @b (cs . Metamorph.R) (n - k)
    where
      k = fromInteger (natVal' @k proxy#)

instance (j ~ GProdLength f, c ~ c', Functor m, GTraceableProd c 1 j z m f)
  => GTraceableSum (WLeaf c') z m (M1 C ('MetaCons c _i _s) f) where
  gtracesum cs _ = M1 <$> gtraceprod @c @1 @j cs

class GTraceableProd n i j z m f where
  gtraceprod :: (GTraceProd n i j f -> z) -> m (f p)

instance
  ( jf ~ GProdLength f
  , Applicative m
  , GTraceableProd n i j z m f
  , GTraceableProd n (i + jf) j z m g )
  => GTraceableProd n i j z m (f :*: g) where
  gtraceprod cs = liftA2 (:*:)
    (gtraceprod @n @i @j (cs . Metamorph.L))
    (gtraceprod @n @(i + jf) @j (cs . Metamorph.R))

instance (Functor m, GTraceableProd n i j z m f)
  => GTraceableProd n i j z m (M1 _i _c f) where
  gtraceprod cs = M1 <$> gtraceprod @n @i @j cs

instance Applicative m => GTraceableProd n i j z m U1 where
  gtraceprod _ = pure U1

instance (Functor m, Traceable z m a)
  => GTraceableProd n i j z m (K1 _i a) where
  gtraceprod cs = K1 <$> trace (cs . GTField)

-- * Pretty

genericPrettyWith
  :: forall mode a
  .  (Generic a, GPretty mode (Rep a))
  => Names -> Int -> a -> ShowS
genericPrettyWith vs n = gPrettyWith @mode vs n . from

class GPretty mode f where
  gPrettyWith :: Names -> Int -> f p -> ShowS

instance GPretty mode f => GPretty mode (M1 D _c f) where
  gPrettyWith vs n (M1 f) = gPrettyWith @mode vs n f

instance (GPretty mode f, GPretty mode g) => GPretty mode (f :+: g) where
  gPrettyWith vs n (L1 f) = gPrettyWith @mode vs n f
  gPrettyWith vs n (R1 g) = gPrettyWith @mode vs n g

instance (KnownSymbol c, GPrettyProd mode f)
  => GPretty mode (M1 C ('MetaCons c 'PrefixI _s) f) where
  gPrettyWith vs n (M1 f) =
    gPrettyProdWith @mode vs f (\_ -> showString (symbolVal' @c proxy#)) n

class GPrettyProd mode f where
  gPrettyProdWith :: Names -> f p -> (Int -> ShowS) -> Int -> ShowS

instance (GPrettyProd mode f, GPrettyProd mode g)
  => GPrettyProd mode (f :*: g) where
  gPrettyProdWith vs (f :*: g) =
    gPrettyProdWith @mode vs g . gPrettyProdWith @mode vs f

instance GPrettyProd mode f => GPrettyProd mode (M1 _i _c f) where
  gPrettyProdWith vs (M1 f) = gPrettyProdWith @mode vs f

instance GPrettyProd mode U1 where
  gPrettyProdWith vs U1 = id

instance Pretty mode a => GPrettyProd mode (K1 _i a) where
  gPrettyProdWith vs (K1 a) s n =
    showParen (n > appPrec) $
      s appPrec .
      showString " " .
      prettyWith @mode vs (appPrec + 1) a
    where
      appPrec = 10

instance
  ( KnownSymbol n
  , KnownNat i
  , KnownNat j
  , PrettyTrace trace )
  => PrettyTrace (GTField n i j trace) where
  prettyTrace (GTField a) vs s =
    prettyTrace a vs $ \n ->
      showParen (n > appPrec) $
        showString ("_" ++ base ++ ix) .
        showString " " .
        s (appPrec + 1)
    where
      base = symbolVal' @n proxy#
      ix | natVal' @j proxy# == 1 = ""
         | otherwise = "_" ++ show (natVal' @i proxy#)
      appPrec = 10
