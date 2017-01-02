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

type F_A a = a -> (a -> a) -> a

f_A :: forall a. F_A a
f_A a r = r a

type A = Metamorph A'
newtype A' = A' (F_A (Metamorph A'))

instance Newtype A' where
  type Old A' = F_A A
  unwrap (A' a) = a

test_A = do
  putStrLn "Example A"
  putStrLn $ "  " ++ show (morphingPure (f_A @A))
  putStrLn $ "  " ++ prettyMorphing "f" (f_A @A)

-- Example B

type F_B b = (Maybe b -> b) -> b

f_B :: forall b. F_B b
f_B f = f (Just (f Nothing))

type B = Metamorph B'
newtype B' = B' (F_B B)

instance Newtype B' where
  type Old B' = F_B B
  unwrap (B' b) = b

test_B = do
  putStrLn "Example B"
  putStrLn $ "  " ++ prettyMorphing "f" (f_B @B)

-- Example C

type F_C c = [c] -> [c]

f_C :: forall c. F_C c
f_C (c1 : c2 : cs) = c2 : c1 : f_C cs
f_C cs = cs

type C = Metamorph C'
newtype C' = C' (F_C C)

instance Newtype C' where
  type Old C' = F_C C
  unwrap (C' c) = c

test_C = do
  putStrLn "Example C:"
  replicateM_ 5 $
    generate g_C >>= \((x,_), c) ->
      putStrLn $ "  " ++ show x ++ " -> " ++ show c
  where
    g_C = morphing (f_C @C)

-- Example D: IO

type F_D d = IO d -> IO [d]

f_D :: forall d. F_D d
f_D io = do
  a <- io
  b <- io
  c <- io
  pure [c, a, b]

type D = Metamorph D'
newtype D' = D' (F_D D)

instance Newtype D' where
  type Old D' = F_D D
  unwrap (D' d) = d

test_D = do
  putStrLn "Example D:"
  d <- morphingIO (f_D @D)
  putStrLn $ "  " ++ show d

-- Example E: IO

type F_E e = IO e -> IO e -> IO [e]

f_E :: forall e. F_E e
f_E a b = do
  w <- a
  x <- b
  y <- b
  z <- a
  pure [w, z, x, y]

type E = Metamorph E'
newtype E' = E' (F_E E)

instance Newtype E' where
  type Old E' = F_E E
  unwrap (E' d) = d

test_E = do
  putStrLn "Example E:"
  (_, e) <- runGenIO (morphing (f_E @E))
  putStrLn $ "  " ++ show e

main = do
  test_A
  test_B
  test_C
  test_D
  test_E
