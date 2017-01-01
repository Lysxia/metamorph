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

type F a = a -> (a -> a) -> a

newtype A = A (F (Retrace A))
type Z = Retrace A

instance Newtype A where
  type Old A = F Z
  unwrap (A a) = a

f :: forall a. F a
f a g = g a

main = do
  -- Gen
  generate (runtrace (f @Z)) >>= print
  -- Identity
  print (runIdentity (runtrace (f @Z)))
