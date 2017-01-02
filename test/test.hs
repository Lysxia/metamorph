{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Monad (replicateM_)
import Data.Functor.Identity
import Test.QuickCheck
import Test.Metamorph

-- Example A

type F a = a -> (a -> a) -> a

_F :: forall a. F a
_F a r = r a

type A = Metamorph A'
newtype A' = A' (F (Metamorph A'))

instance Newtype A' where
  type Old A' = F A
  unwrap (A' a) = a

test_F = do
  putStrLn "Example A"
  putStrLn $ "  " ++ show (morphingPure (_F @A))
  putStrLn $ "  " ++ prettyMorphing "_F" (_F @A)

-- Example B

type G b = (Maybe b -> b) -> b

_G :: forall b. G b
_G f = f (Just (f Nothing))

type B = Metamorph B'
newtype B' = B' (G B)

instance Newtype B' where
  type Old B' = G B
  unwrap (B' b) = b

test_G = do
  putStrLn "Example B"
  putStrLn $ "  " ++ prettyMorphing "_G" (_G @B)

-- Example C

type H c = [c] -> [c]

_H :: forall c. H c
_H (c1 : c2 : cs) = c2 : c1 : _H cs
_H cs = cs

type C = Metamorph C'
newtype C' = C' (H C)

instance Newtype C' where
  type Old C' = H C
  unwrap (C' c) = c

test_C = do
  putStrLn "Example C:"
  replicateM_ 5 $
    generate g_C >>= \c -> putStrLn $ "  " ++ show c
  where
    g_C = morphing (_H @C)

main = do
  test_F
  test_G
  test_C
