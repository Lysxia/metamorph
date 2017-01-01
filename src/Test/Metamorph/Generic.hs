{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Test.Metamorph.Generic where

import GHC.Generics
import GHC.TypeLits

type family ProductCont r (as :: [*]) :: * where
  ProductCont r '[] = r
  ProductCont r (a ': as) = a -> ProductCont r as

-- | Generic CPS representation of product types.
type Product r as = ProductCont r as -> r

-- | Generic CPS representation of sum types.
type family Sum r (as :: [*]) :: * where
  Sum r '[] = r
  Sum r (a ': as) = (a -> r) -> Sum r as

-- | Generic CPS representation of sum types, with type-level tags.
data family Sum' r (as :: [(Symbol, *)]) :: *
newtype instance Sum' r '[] = TagEmpty r
newtype instance Sum' r ('(n, a) ': as)
  = TagPlus ((a -> r) -> Sum' r as)

newtype TraceGeneric a
  = TraceGeneric (forall r. GenericSumTrace r (Rep a))

type GenericSumTrace r rep = Sum' r (GenericSumList r rep)

type family GenericSumList (r :: *) (rep :: * -> *) :: [(Symbol, *)] where
  GenericSumList r (f :+: g)
    = '(GenericConstrName f, GenericProductTrace r f) ': GenericSumList r g
  GenericSumList r (M1 i c f)
    = '[ '(GenericConstrName (M1 i c f), GenericProductTrace r f) ]

type family GenericConstrName (rep :: * -> *) :: Symbol where
  GenericConstrName (M1 C ('MetaCons c _ _) f) = c

type GenericProductTrace r rep = Sum' r (GenericProductList r rep)

type family GenericProductList (r :: *) (rep :: * -> *) :: [(Symbol, *)] where
  GenericProductList r (M1 _ _ f) = GenericProductList r f
  GenericProductList r (f :*: g) =
    '(GenericFieldName f, GenericFieldTrace r f) ': GenericProductList r g

type family GenericFieldName (rep :: * -> *) :: Symbol where
  GenericFieldName (M1 S ('MetaSel ('Just n) _ _ _) _) = n
  GenericFieldName (M1 S ('MetaSel 'Nothing _ _ _) _) = "???"

type family GenericFieldTrace (r :: *) (rep :: * -> *) :: * where

