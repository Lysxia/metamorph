module Test.Metamorph
  ( morphing
  , morphingPure
  , morphingGen
  , morphingIO
  , Metamorph
  , Newtype(..)
  , module Test.Metamorph.Pretty
  , GenIO
  , runGenIO
  -- * Generics
  , TraceOf
  , Traceable(..)
  , GTraceOf
  , genericTrace
  , genericPrettyWith
  ) where

import Test.Metamorph.Generic
import Test.Metamorph.Internal
import Test.Metamorph.IO
import Test.Metamorph.Pretty
