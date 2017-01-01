module Notes where

newtype Fix f = Fix (f (Fix f))

-- data [a] = [] | a : [a]

-- [a]
data Z1 a = ConsL | ConsR (Z1 a)

-- z -> a
data ZFun z a = FunApp z

-- a -> a
data ZEndo a = EndoApp a

-- a -> [a]
data ZEndoList a = EndoListApp a (Z1 a)

type T1 a = [a] -> [a]

type (f :*: g) a = (f a, g a)
type (f :+: g) a = L1 a | R1 a
type (f :-> g) a = f a -> g a
type Id a = a
type Unit a = Unit

-- Given (f :: * -> *)
-- find (A :: *) such that (f A) embeds (forall a. f a)
--
-- There are
-- > embed :: forall a. f a -> f A
-- > project :: f A -> forall a. f a
--
-- such that
-- > project . embed = id
--
-- f A ~> forall a. f a
--
-- For y, z :: forall a. f a
-- z = y
-- iff
-- z = y :: f A

-- Given (f, g :: * -> *)
-- find (A :: *) such that,
-- for all (p, q :: forall a. f a -> g a)
--
-- if
--   for all (z :: f A), p z = q z
-- then
--   for all a. forall (z :: f a). p z = q z
--

type family K f a

K (f :+: g) a
  = KL1 (K f a)
  | KR1 (K g a)
K (f :*: g) a
  = KProd1 (K f a)
  | KProd2 (K g a)
K (f :-> g) a
  = KArg (F f a)
  | KRes (K g a)
K Id             -- Void
K Unit a         -- Void

type family F f a

F (f :+: g) a
  = FL1 (F f a)
  | FR1 (F g a)
F (f :*: g) a
  = FProd1 (F f a)
  | FProd2 (F g a)
F (f :-> g) a
  = FFun (f a) (F g a)
F Id = FId
F Unit a             -- Void

data F' a
  Root :: F' a
  FL1 :: F' b a -> F' (f :+: g -. b) a
  FL2 :: F' b a -> 
  FId :: F' b a -> F' (Id -> b) a

f a -> g a -> Either a a
                     ^

L (App (g a) (App (f a) (...)))

Root :: Trace [A f0] (A f0)
App :: Trace [] a 

type family A f

A f = Fix (K f)

type family Sample f

Sample (f :+: g) a
  = SL1 (Sample f a)
  | SR1 (Sample g a)
Sample (f :*: g) a
  = SProd1 (Sample f a)
  | SProd2 (Sample g a)
Sample (f :-> g) a
  = SFun (f a) (Sample g a)
Sample Id a = SId a
Sample Unit a = SUnit

cogenerate {f0} (f :: * -> *)
  :: (K f (A f0) -> A f0) -> (Sample f (A f0) -> Gen r) -> f A -> Gen r
cogenerate (f :+: g) k h (L1 p) = cogenerate f (k . KL1) (h . SL1) p
cogenerate (f :+: g) k h (R1 p) = cogenerate g (k . KR1) (h . SL2) p
cogenerate (f :*: g) k h (p :*: q)
  = oneOf
      [ cogenerate f (k . KProd1) (h . SProd1) p
      , cogenerate f (k . KProd2) (h . SProd2) q ]
cogenerate (f :-> g) k h p = do
  fa <- generate f k
  cogenerate g (k . KRes) (h . SFun fa) (p fa)
cogenerate Id k a = h (SId a)
cogenerate Unit k p = h SUnit

generate {f0} (f :: * -> *) :: (F f (A f0) -> A f0) -> Gen (f (A f0))
generate (f :+: g) k = oneOf [generate f (k . L1), generate g (k . R1)]
generate (f :*: g) k = liftA2 (,) (generate f (k . FProd1)) (generate g (k . FProd2))
generate (f :-> g) k = generateFun f $ \pf -> generate g (k . FFun pf)
generate Id k = pure (k FId)
generate Unit k = empty

generateFun {f0} (f :: * -> *) :: (f (A f0) -> Gen (g (A f0))) -> Gen ((f :-> g) (A f0))
generateFun f fun = (...) -- coarbitrary stuff
