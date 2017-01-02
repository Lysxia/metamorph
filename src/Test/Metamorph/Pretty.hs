-- | Pretty printing symbolic values.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Metamorph.Pretty where

import Control.Applicative (liftA2)
import Data.Function (fix)
import Data.Functor.Identity
import Data.List (intersperse)
import GHC.Exts (proxy#)
import GHC.Generics
import GHC.TypeLits
import Text.Show

import Test.Metamorph.Generic
import Test.Metamorph.Internal

-- | A list of variable names to represent function parameters.
type Names = [String]

defaultNames :: Names
defaultNames = tail (fix (\f -> "" : liftA2 (flip (:)) f ['a' .. 'z']))

pretty :: Pretty t => t -> String
pretty t = prettyWith defaultNames 0 t ""

instance Pretty (Metamorph a) => Show (Metamorph a) where
  showsPrec = prettyWith defaultNames

class Pretty t where
  prettyWith :: Names -> Int -> t -> ShowS

  default prettyWith
    :: (Generic t, PrettyGeneric (Rep t))
    => Names -> Int -> t -> ShowS
  prettyWith vs n = prettyGeneric vs n . from

class PrettyGeneric f where
  prettyGeneric :: Names -> Int -> f p -> ShowS

instance (Newtype a, PrettyRetrace (Retrace (Old a)))
  => Pretty (Metamorph a) where
  prettyWith vs n (Metamorph a) = prettyRetrace (a ()) vs vs n

-- instance (PrettyTrace trace, PrettyRetrace retrace)
--   => Pretty (RetraceFun trace retrace) where
--   prettyWith a vs = prettyRetrace a vs vs

instance Pretty a => Pretty (Maybe a) where
  prettyWith _ _ Nothing = showString "Nothing"
  prettyWith vs n (Just a) = showParen (n > appPrec) $
    showString "Just " . prettyWith vs (appPrec + 1) a
    where
      appPrec = 10

instance Pretty a => Pretty [a] where
  prettyWith vs _ as =
    showString "[" .
    prettyCommaSep vs as .
    showString "]"

prettyCommaSep :: Pretty a => Names -> [a] -> ShowS
prettyCommaSep vs =
  foldr (.) id .
  intersperse (showString ",") .
  fmap (prettyWith vs 0)

-- * Showing Trace.

class PrettyTrace t where
  prettyTrace :: t -> Names -> (Int -> ShowS) -> Int -> ShowS

class PrettySum as where
  prettySum
    :: Sum' (Names -> (Int -> ShowS) -> Int -> ShowS) as
    -> Names -> (Int -> ShowS) -> Int -> ShowS

instance PrettySum as
  => PrettyTrace (TraceSimple n0 as) where
  prettyTrace (TraceSimple t) = prettySum t

instance PrettySum '[] where
  prettySum (TagEmpty s) = s

-- <trace> (unCons (...))
instance (KnownSymbol n, PrettyTrace a, PrettySum as)
  => PrettySum ('(n, a) ': as) where
  prettySum (TagPlus f) = prettySum . f $ \ta vs s ->
    prettyTrace ta vs $ \n ->
      showParen (n > appPrec) $
        showString (symbolVal' @n proxy#) .
        showString " " .
        s (appPrec + 1)
    where appPrec = 10

-- <trace> ((...) a)
instance (Pretty a, PrettyTrace trace)
  => PrettyTrace (TraceFun a trace) where
  prettyTrace (TraceFun f) = f $ \a tb vs s ->
    prettyTrace tb vs $ \n ->
      showParen (n > appPrec) $
        s appPrec .
        showString " " .
        prettyWith vs (appPrec + 1) a
    where
      appPrec = 10

-- <trace> ((...) !! n)
instance PrettyTrace trace
  => PrettyTrace (TraceList trace) where
  prettyTrace (TraceList f) = f $ \i ta vs s ->
    prettyTrace ta vs $ \n -> showParen (n > ixPrec) $
      s (ixPrec + 1) .
      showString " !! " .
      shows i
    where
      ixPrec = 9

instance PrettyTrace TraceEnd where
  prettyTrace _ _ = id

-- * Showing Retrace

class PrettyRetrace t where
  prettyRetrace :: t -> Names -> Names -> Int -> ShowS

instance (PrettyTrace trace, PrettyRetrace retrace)
  => PrettyRetrace (RetraceFun trace retrace) where
  prettyRetrace (RetraceFun f) allVs (v : vs) = f
    (\t -> prettyTrace t allVs (\_ -> showString v))
    (\rt -> prettyRetrace rt allVs vs)

class PrettyRetraceSum as where
  prettyRetraceSum
    :: Sum' (Names -> Names -> Int -> ShowS) as
    -> Names -> Names -> Int -> ShowS

instance PrettyRetraceSum '[] where
  prettyRetraceSum (TagEmpty r) = r

instance (PrettyRetrace a, PrettyRetraceSum as)
  => PrettyRetraceSum ('(n, a) ': as) where
  prettyRetraceSum (TagPlus f) = prettyRetraceSum (f prettyRetrace)

instance PrettyRetraceSum as => PrettyRetrace (RetraceSimple n0 as) where
  prettyRetrace (RetraceSimple f) = prettyRetraceSum f

instance PrettyRetrace retrace => PrettyRetrace (RetraceList retrace) where
  prettyRetrace (RetraceList f) = f
    (\_ rt -> prettyRetrace rt)

-- | Naming the left-hand side of a function
class RunExpr a where
  runExpr :: Expr a -> Expr (Untrace a)

instance RunExpr b => RunExpr (a -> b) where
  runExpr (Expr (v : vs) s) =
    runExpr @b . Expr vs $ \n ->
      showParen (n > appPrec) $
        s appPrec .
        showString " " .
        showString v
    where
      appPrec = 10

instance RunExpr () where
  runExpr = id

instance RunExpr Bool where
  runExpr = id

instance RunExpr Integer where
  runExpr = id

instance RunExpr Int where
  runExpr = id

instance RunExpr (a, b) where
  runExpr = id

instance RunExpr (Either a b) where
  runExpr = id

instance RunExpr (Maybe a) where
  runExpr = id

instance RunExpr [c] where
  runExpr = id

instance RunExpr (Metamorph a) where
  runExpr = id

data Expr a = Expr Names (Int -> ShowS)

newExpr :: forall a. String -> Names -> Expr a
newExpr f vs = Expr vs (\_ -> showString f)

prettyMorphingWithExpr
  :: (Morphing (Retrace a) Identity a, Pretty (Untrace a), RunExpr a)
  => Expr a -> Untrace a -> String
prettyMorphingWithExpr e@(Expr vs _) a =
  s 0 . showString " = " . prettyWith vs 0 a $ ""
  where
    Expr _ s = runExpr e

prettyMorphingWith
  :: forall a
  .  (Morphing (Retrace a) Identity a, Pretty (Untrace a), RunExpr a)
  => Names -> a -> String
prettyMorphingWith (f : vs) a =
  prettyMorphingWithExpr @a (newExpr f vs) (morphingPure a)

prettyMorphing
  :: (Morphing (Retrace a) Identity a, Pretty (Untrace a), RunExpr a)
  => String -> a -> String
prettyMorphing f = prettyMorphingWith (f : filter (/= f) defaultNames)
