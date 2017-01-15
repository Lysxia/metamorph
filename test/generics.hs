{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import Control.Monad (replicateM_)
import GHC.Generics (Generic, Rep)
import Test.QuickCheck
import Test.Metamorph

-- Example: Generics

data Three a = Zero | One a | Two a a | Three a a a | Four (Three a)
  deriving (Eq, Ord, Show, Generic)

instance Pretty mode a => Pretty mode (Three a) where
  prettyWith = genericPrettyWith @mode

type instance TraceOf (Three a) = GTraceOf (Rep (Three a))

instance Traceable z Gen a => Traceable z Gen (Three a) where
  trace = genericTrace

type F a = Three a -> [a]

f :: forall a. F a
f Zero = []
f (One a) = [a]
f (Two a b) = [a, b]
f (Three a b c) = [a, b, c]
f (Four d) = f d

type A = Metamorph A'
newtype A' = A' (F A)

instance Newtype A' where
  type Old A' = F A
  unwrap (A' f) = f

main =
  replicateM_ 5 $
    generate g >>= \((x,_), a) ->
      putStrLn $ "  a@" ++ prettyShape 11 x "" ++ " -> " ++ show a
  where
    g = morphing (f @A)
