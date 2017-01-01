{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Functor.Identity
import Test.QuickCheck
import Test.Metamorph

-- Example A

type F a = a -> (a -> a) -> a

_F :: forall a. F a
_F a r = r a

type A = Retrace A'
newtype A' = A' (F (Retrace A'))

instance Newtype A' where
  type Old A' = F A
  unwrap (A' a) = a

test_F = generate g_A >>= print
  where
    g_A = runtrace (_F @A) :: Gen A

-- Example B

type G b = (Maybe b -> b) -> b

_G :: forall b. G b
_G f = f (Just (f Nothing))

type B = Retrace B'
newtype B' = B' (G B)

instance Newtype B' where
  type Old B' = G B
  unwrap (B' b) = b

test_G = print (runIdentity i_B)
  where
    i_B = runtrace (_G @B) :: Identity B

-- Example C

type H c = [c] -> [c]

_H :: forall c. H c
_H (c1 : c2 : cs) = c2 : c1 : _H cs
_H cs = cs

type C = Retrace C'
newtype C' = C' (H C)

instance Newtype C' where
  type Old C' = H C
  unwrap (C' c) = c

test_C = generate g_C >>= print
  where
    g_C = runtrace (_H @C)

main = do
  test_F
  test_G
  test_C
