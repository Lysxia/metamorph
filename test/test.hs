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

-- Assert that two strings are equal and print them.
(=?) :: String -> String -> IO ()
a =? b | a == b = putStrLn $ "  " ++ a
a =? b = do
  putStrLn $ "E<" ++ a
  putStrLn $ "E>" ++ b

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
  show (morphingPure (f_A @A)) =? "b a"
  prettyMorphing "f" (f_A @A)  =? "f a b = b a"

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
  prettyMorphing "f" (f_B @B) =? "f a = a (Just (a Nothing))"

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
      putStrLn $ "  a@" ++ pretty_ x ++ " -> " ++ show c
  where
    g_C = resize 10 $ morphing (f_C @C)

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
  show d =? "[runIO<3> a,runIO<1> a,runIO<2> a]"

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
  e1 <- morphingIO (f_E @E)
  show e1 =? "[runIO<1> a,runIO<2> a,runIO<1> b,runIO<2> b]"
  (_, e2) <- runGenIO (morphing (f_E @E))
  show e2 =? "[runIO<1,1> a,runIO<4,2> a,runIO<2,1> b,runIO<3,2> b]"

main = do
  test_A
  test_B
  test_C
  test_D
  test_E

