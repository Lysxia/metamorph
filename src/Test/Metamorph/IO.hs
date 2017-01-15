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
-- @GenIO@ adds a global counter to keep track of the ordering of
-- all @IO@ actions together.
--
-- > do { a <- runGenIO $ morphing (f @A) ; print a }
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

data TraceIO trace
  = TraceIO (Maybe Int) Int trace
  deriving (Eq, Ord, Show)

type instance TraceOf (IO a) = TraceIO (Trace a)

instance Traceable z IO a => Traceable z IO (IO a) where
  trace cs = do
    r <- newIORef 0
    pure $ do
      n <- incr r
      trace (cs .+ TraceIO Nothing n)

type instance Codomain (IO a) = a

instance MonadIO m => Morphing z m (IO a) where
  morphing' _ = fmap ((,) ()) . liftIO

instance PrettyTrace trace => PrettyTrace (TraceIO trace) where
  prettyTrace (TraceIO i j tb) vs s =
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
newtype GenIO a = GenIO { runGenIO_ :: IORef Int -> IO a }

runGenIO :: GenIO a -> IO a
runGenIO tio = newIORef 0 >>= runGenIO_ tio

instance Functor GenIO where
  fmap f (GenIO io) = GenIO (fmap f . io)

instance Applicative GenIO where
  pure = GenIO . pure . pure
  GenIO f <*> GenIO a = GenIO (liftA2 (<*>) f a)

instance Monad GenIO where
  GenIO a_ >>= f = GenIO $ \r ->
    a_ r >>= \a -> runGenIO_ (f a) r

instance MonadIO GenIO where
  liftIO io = GenIO (const io)

instance Traceable z GenIO a => Traceable z GenIO (IO a) where
  trace cs = GenIO $ \r0 -> do
      r <- newIORef 0
      pure $ do
        n0 <- incr r0
        n <- incr r
        runGenIO_ (trace (cs .+ TraceIO (Just n0) n)) r0

morphingIO :: Morphing (Retrace e) IO e => e -> IO (Codomain e)
morphingIO = fmap snd . morphing
