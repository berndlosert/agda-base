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
  constructor toProduct
  field getProduct : a

open Product public

instance
  Semigroup-Product-Nat : Semigroup (Product Nat)
  Semigroup-Product-Nat ._<>_ m n = toProduct (getProduct m * getProduct n)

  Semigroup-Product-Int : Semigroup (Product Int)
  Semigroup-Product-Int ._<>_ m n = toProduct (getProduct m * getProduct n)

  Monoid-Product-Nat : Monoid (Product Nat)
  Monoid-Product-Nat .mempty = toProduct 1

  Monoid-Product-Int : Monoid (Product Int)
  Monoid-Product-Int .mempty = toProduct 1

  Functor-Product : Functor Product
  Functor-Product .map f = toProduct <<< f <<< getProduct

  Applicative-Product : Applicative Product
  Applicative-Product .pure = toProduct
  Applicative-Product ._<*>_ f x = toProduct $ (getProduct f) (getProduct x)

  Monad-Product : Monad Product
  Monad-Product ._>>=_ (toProduct x) k = k x

  Show-Product : {{Show a}} -> Show (Product a)
  Show-Product .showsPrec d x = showParen (d > appPrec) $
    showString "toProduct " <<< showsPrec appPrec+1 (getProduct x)
