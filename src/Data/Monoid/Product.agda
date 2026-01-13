module Data.Monoid.Product where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Literals
-------------------------------------------------------------------------------

instance
  _ = FromNat-Int
  _ = FromNat-Float

-------------------------------------------------------------------------------
-- Product
-------------------------------------------------------------------------------

-- For Multiplicable semigroups, monoids, etc.
record Product (a : Type) : Type where
  constructor asProduct
  field getProduct : a

open Product public

instance
  Semigroup-Product-Nat : Semigroup (Product Nat)
  Semigroup-Product-Nat ._<>_ x y = asProduct (getProduct x * getProduct y)

  Monoid-Product-Nat : Monoid (Product Nat)
  Monoid-Product-Nat .mempty = asProduct 1

  Semigroup-Product-Nat1 : Semigroup (Product Nat1)
  Semigroup-Product-Nat1 ._<>_ (asProduct m) (asProduct n) = asProduct (m * n)

  Monoid-Product-Nat1 : Monoid (Product Nat1)
  Monoid-Product-Nat1 .mempty = asProduct (suc 0)

  Semigroup-Product-Int : Semigroup (Product Int)
  Semigroup-Product-Int ._<>_ x y = asProduct (getProduct x * getProduct y)

  Monoid-Product-Int : Monoid (Product Int)
  Monoid-Product-Int .mempty = asProduct 1

  Semigroup-Product-Float : Semigroup (Product Float)
  Semigroup-Product-Float ._<>_ x y = asProduct (getProduct x * getProduct y)

  Monoid-Product-Float : Monoid (Product Float)
  Monoid-Product-Float .mempty = asProduct 1

  Functor-Product : Functor Product
  Functor-Product .map f = asProduct <<< f <<< getProduct

  Applicative-Product : Applicative Product
  Applicative-Product .pure = asProduct
  Applicative-Product ._<*>_ f x = asProduct $ (getProduct f) (getProduct x)

  Monad-Product : Monad Product
  Monad-Product ._>>=_ (asProduct x) k = k x

  Show-Product : {{Show a}} -> Show (Product a)
  Show-Product .show = showDefault
  Show-Product .showsPrec prec (asProduct x) =
    showsUnaryWith showsPrec "asProduct" prec x