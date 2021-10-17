{-# OPTIONS --type-in-type #-}

module Data.Monoid.Product where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Product
-------------------------------------------------------------------------------

-- For multiplicative semigroups, monoids, etc.
record Product (a : Set) : Set where
  constructor aProduct
  field getProduct : a

open Product public

instance
  Semigroup-Product-Nat : Semigroup (Product Nat)
  Semigroup-Product-Nat ._<>_ m n = aProduct (getProduct m * getProduct n)

  Semigroup-Product-Int : Semigroup (Product Int)
  Semigroup-Product-Int ._<>_ m n = aProduct (getProduct m * getProduct n)

  Monoid-Product-Nat : Monoid (Product Nat)
  Monoid-Product-Nat .mempty = aProduct 1

  Monoid-Product-Int : Monoid (Product Int)
  Monoid-Product-Int .mempty = aProduct 1

  Functor-Product : Functor Product
  Functor-Product .map f = aProduct <<< f <<< getProduct

  Applicative-Product : Applicative Product
  Applicative-Product .pure = aProduct
  Applicative-Product ._<*>_ f x = aProduct $ (getProduct f) (getProduct x)

  Monad-Product : Monad Product
  Monad-Product ._>>=_ (aProduct x) k = k x

  Show-Product : {{Show a}} -> Show (Product a)
  Show-Product .showsPrec prec x = showParen (prec > appPrec) $
    showString "aProduct " <<< showsPrec appPrec+1 (getProduct x)
