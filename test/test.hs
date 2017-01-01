{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

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

newtype instance Retrace A = RetraceA (forall r. Sum r '[])

instance PrettyRetrace A where
  prettyRetrace (RetraceA f) = f

instance CoArbitraryRetrace A where
  car (RetraceA f) = f

type instance Trace A = TraceEnd

instance Applicative m => Traceable Z m A where
  trace = traceEnd A

generateA :: (forall a. F a) -> Gen A
generateA f = do
  a0 <- trace @Z @Gen @A (\ta ret -> ret (RFun $ \k _ -> k ta))
  a1 <- trace @Z @Gen @(A -> A) (\ta1 ret -> ret (RFun $ \_ k -> k (RFun $ \k _ -> k ta1)))
  pure (f a0 a1)

f :: forall a. F a
f a g = g a

main = generate (generateA f) >>= print
