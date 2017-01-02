-- | Metamorph can work with functions taking @IO@ values as arguments!
--
-- Every generated @IO@ action has a counter which is incremented at every
-- execution, so that values produced by each execution can be distinguished.
--
-- > f :: IO a -> IO a -> IO (a, a, a, a)
-- > f a b = do
-- >   x1 <- a
-- >   y1 <- b
-- >   x2 <- a
-- >   y2 <- b
-- >   pure (x1, x2, y2, y1)
--
-- > do { a <- morphing (f @A) ; print a }
--
-- > Output: (runIO<1> a,runIO<2> a,runIO<2> b, runIO<1> b)
--
-- Note that this only gives an ordering between executions of the same action.
--
-- @TickIO@ adds a global counter to keep track of the ordering of
-- all @IO@ actions together.
--
-- > do { a <- runTickIO $ morphing (f @A) ; print a }
--
-- > Output: (runIO<1,1> a,runIO<3,2> a,runIO<4,2> b,runIO<2,1> b)

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Metamorph.IO where

import Control.Applicative (liftA2)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Coerce (coerce)
import Data.IORef (IORef, newIORef, modifyIORef', readIORef)

import Test.Metamorph.Generic
import Test.Metamorph.Internal
import Test.Metamorph.Pretty

incr :: IORef Int -> IO Int
incr r = modifyIORef' r (+ 1) >> readIORef r

newtype TraceIO trace
  = TraceIO (forall r. ProductCont r '[ Maybe Int, Int, trace ] -> r)

type instance Trace (IO a) = TraceIO (Trace a)

instance Traceable z IO a => Traceable z IO (IO a) where
  trace cs = do
    r <- newIORef 0
    pure $ do
      n <- incr r
      trace (cs . ap n)
    where
      ap n ta = TraceIO (\k -> k Nothing n ta)

type instance Retrace (IO a) = RetraceSimple "IO" '[
  '("IO *", Retrace a)]

type instance Untrace (IO a) = a

instance MonadIO m => Morphing z m (IO a) where
  morphing' _ = liftIO

instance PrettyTrace trace => PrettyTrace (TraceIO trace) where
  prettyTrace (TraceIO f) = f $ \i j tb vs s ->
    prettyTrace tb vs $ \n ->
      showParen (n > appPrec) $
        showString ("runIO<" ++ show' i ++ show j ++ "> ") .
        s (appPrec + 1)
    where
      appPrec = 10
      show' Nothing = ""
      show' (Just i) = show i ++ ","

instance RunExpr (IO a) where
  runExpr = coerce

-- | A context in which to generate @IO@ actions.
-- See 'Test.Metamorph.IO' (@Test.Metamorph.IO@).
newtype TickIO a = TickIO { runTickIO_ :: IORef Int -> IO a }

runTickIO :: TickIO a -> IO a
runTickIO tio = newIORef 0 >>= runTickIO_ tio

instance Functor TickIO where
  fmap f (TickIO io) = TickIO (fmap f . io)

instance Applicative TickIO where
  pure = TickIO . pure . pure
  TickIO f <*> TickIO a = TickIO (liftA2 (<*>) f a)

instance Monad TickIO where
  TickIO a_ >>= f = TickIO $ \r ->
    a_ r >>= \a -> runTickIO_ (f a) r

instance MonadIO TickIO where
  liftIO io = TickIO (const io)

instance Traceable z TickIO a => Traceable z TickIO (IO a) where
  trace cs = TickIO $ \r0 -> do
      r <- newIORef 0
      pure $ do
        n0 <- incr r0
        n <- incr r
        let ap ta = TraceIO (\k -> k (Just n0) n ta)
        runTickIO_ (trace (cs . ap)) r0
