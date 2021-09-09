{-# OPTIONS --type-in-type #-}

module Data.Monoid.Product where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

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
  constructor toProduct
  field getProduct : a

open Product public

instance
  Semigroup-Product-Nat : Semigroup (Product Nat)
  Semigroup-Product-Nat ._<>_ (toProduct m) (toProduct n) = toProduct (m * n)

  Semigroup-Product-Int : Semigroup (Product Int)
  Semigroup-Product-Int ._<>_ (toProduct m) (toProduct n) = toProduct (m * n)

  Monoid-Product-Nat : Monoid (Product Nat)
  Monoid-Product-Nat .neutral = toProduct 1

  Monoid-Product-Int : Monoid (Product Int)
  Monoid-Product-Int .neutral = toProduct 1

  Functor-Product : Functor Product
  Functor-Product .map f = toProduct <<< f <<< getProduct

  Applicative-Product : Applicative Product
  Applicative-Product .pure = toProduct
  Applicative-Product ._<*>_ (toProduct f) (toProduct x) = toProduct (f x)

  Monad-Product : Monad Product
  Monad-Product ._>>=_ (toProduct x) k = k x

  Show-Product : {{Show a}} -> Show (Product a)
  Show-Product .showsPrec d (toProduct x) = showParen (d > appPrec)
    (showString "toProduct " <<< showsPrec appPrec+1 x)
