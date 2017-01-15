-- | Pretty printing symbolic values.
--
-- This module turns a 'Trace' into a Haskell expression of type @'Metamorph' a@.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import GHC.TypeLits
import Text.Show

import Test.Metamorph.Internal

-- | A list of variable names to represent function parameters.
type Names = [String]

data Mode = Detail | Shape

defaultNames :: Names
defaultNames = tail (fix (\f -> "" : liftA2 (flip (:)) f ['a' .. 'z']))

pretty :: Pretty 'Detail t => t -> String
pretty t = prettyDetail defaultNames 0 t ""

pretty_ :: Pretty 'Shape t => t -> String
pretty_ t = prettyShape 0 t ""

prettyDetail :: Pretty 'Detail t => Names -> Int -> t -> ShowS
prettyDetail = prettyWith @'Detail

prettyShape :: Pretty 'Shape t => Int -> t -> ShowS
prettyShape = prettyWith @'Shape []  -- Not used by Shape

instance Pretty 'Detail (Metamorph a) => Show (Metamorph a) where
  showsPrec = prettyDetail defaultNames

-- | Conversion to 'String' parameterized by a list of variable names,
-- used in the 'Detail' mode, and ignored in the 'Shape' mode.
class Pretty (mode :: Mode) t where
  prettyWith :: Names -> Int -> t -> ShowS

instance (Newtype a, PrettyRetrace (Old a))
  => Pretty Detail (Metamorph a) where
  prettyWith vs n (Metamorph a) = prettyRetrace @(Old a) (a ()) vs vs n

instance Pretty 'Shape (Metamorph a) where
  prettyWith _ _ _ = showString "_"

instance Pretty mode a => Pretty mode (Maybe a) where
  prettyWith _ _ Nothing = showString "Nothing"
  prettyWith vs n (Just a) = showParen (n > appPrec) $
    showString "Just " . prettyWith @mode vs (appPrec + 1) a
    where
      appPrec = 10

instance Pretty mode a => Pretty mode [a] where
  prettyWith vs _ as =
    showString "[" .
    prettyCommaSep @mode vs as .
    showString "]"

prettyCommaSep
  :: forall mode a. Pretty mode a => Names -> [a] -> ShowS
prettyCommaSep vs =
  foldr (.) id .
  intersperse (showString ",") .
  fmap (prettyWith @mode vs 0)

-- * Showing Trace.

class PrettyTrace t where
  prettyTrace :: t -> Names -> (Int -> ShowS) -> Int -> ShowS

instance (PrettyTrace a, PrettyTrace b) => PrettyTrace (a :+: b) where
  prettyTrace (L a) = prettyTrace a
  prettyTrace (R b) = prettyTrace b

instance PrettyTrace Void where
  prettyTrace = absurd

-- <trace> (unCons (...))
instance (KnownSymbol n, PrettyTrace a) => PrettyTrace (TField n a) where
  prettyTrace (TField a) vs s =
    prettyTrace a vs $ \n ->
      showParen (n > appPrec) $
        showString (symbolVal' @n proxy#) .
        showString " " .
        s (appPrec + 1)
    where
      appPrec = 10

-- <trace> ((...) a)
instance (Pretty 'Detail a, PrettyTrace trace)
  => PrettyTrace (TraceFun a trace) where
  prettyTrace (TraceFun a tb) vs s =
    prettyTrace tb vs $ \n ->
      showParen (n > appPrec) $
        s appPrec .
        showString " " .
        prettyDetail vs (appPrec + 1) a
    where
      appPrec = 10

-- <trace> ((...) !! n)
instance PrettyTrace trace
  => PrettyTrace (TraceList trace) where
  prettyTrace (TraceList i ta) vs s =
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
  prettyRetrace :: Retrace t -> Names -> Names -> Int -> ShowS

instance (PrettyTrace (Trace a), PrettyRetrace b)
  => PrettyRetrace (a -> b) where
  prettyRetrace (L (TField ta)) allVs (v : _) = 
    prettyTrace ta allVs (\_ -> showString v)
  prettyRetrace (R (TField rtb)) allVs (_ : vs) = 
    prettyRetrace @b rtb allVs vs

instance PrettyRetrace (IO a) where
  prettyRetrace _ = error "Unimplemented"

instance PrettyRetrace (a, b) where
  prettyRetrace _ = error "Unimplemented"

instance PrettyRetrace (Either a b) where
  prettyRetrace _ = error "Unimplemented"

instance PrettyRetrace (Maybe a) where
  prettyRetrace _ = error "Unimplemented"

instance PrettyRetrace [c] where
  prettyRetrace _ = error "Unimplemented"

instance PrettyRetrace (Metamorph a) where
  prettyRetrace void = absurd void

instance PrettyRetrace () where
  prettyRetrace void = absurd void

instance PrettyRetrace Bool where
  prettyRetrace void = absurd void

instance PrettyRetrace Integer where
  prettyRetrace void = absurd void

instance PrettyRetrace Int where
  prettyRetrace void = absurd void

-- | Naming the left-hand side of a function
class RunExpr a where
  runExpr :: Expr a -> Expr (Codomain a)

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
  :: (Morphing (Retrace a) Identity a, Pretty 'Detail (Codomain a), RunExpr a)
  => Expr a -> Codomain a -> String
prettyMorphingWithExpr e@(Expr vs _) a =
  s 0 . showString " = " . prettyDetail vs 0 a $ ""
  where
    Expr _ s = runExpr e

prettyMorphingWith
  :: forall a
  .  (Morphing (Retrace a) Identity a, Pretty 'Detail (Codomain a), RunExpr a)
  => Names -> a -> String
prettyMorphingWith (f : vs) a =
  prettyMorphingWithExpr @a (newExpr f vs) (morphingPure a)

prettyMorphing
  :: (Morphing (Retrace a) Identity a, Pretty 'Detail (Codomain a), RunExpr a)
  => String -> a -> String
prettyMorphing f = prettyMorphingWith (f : filter (/= f) defaultNames)
