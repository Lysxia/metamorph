{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Functor.Identity
import Test.QuickCheck
import Test.Metamorph

type F a = a -> (a -> a) -> a

type Z = Retrace (F A)

newtype A = A Z

instance Show A where
  showsPrec n (A z) = showParen True $
    showsPrec 11 z . showString " :: A"

instance CoArbitrary A where
  coarbitrary (A z) = car z

-- | Void type.
newtype instance Retrace A = RetraceA (forall r. Sum r '[])

-- | Void instance.
instance PrettyRetrace A where
  prettyRetrace (RetraceA f) = f

-- | Void instance.
instance CoArbitraryRetrace A where
  car (RetraceA f) = f

type instance Trace A = TraceEnd

instance Applicative m => Traceable Z m A where
  trace = traceEnd A

type instance Untrace A = A

instance Applicative m => RunTrace z m A where
  runtrace' _ a = pure a

generateA :: (forall a. F a) -> Gen A
generateA = runtrace @(F A)

f :: forall a. F a
f a g = g a

main = do
  generate (runtrace (f @A)) >>= print
  print (runIdentity (runtrace (f @A)))
