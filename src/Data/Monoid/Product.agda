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
  constructor Product:
  field getProduct : a

open Product public

instance
  Semigroup-Product-Nat : Semigroup (Product Nat)
  Semigroup-Product-Nat ._<>_ (Product: m) (Product: n) = Product: (m * n)

  Semigroup-Product-Int : Semigroup (Product Int)
  Semigroup-Product-Int ._<>_ (Product: m) (Product: n) = Product: (m * n)

  Monoid-Product-Nat : Monoid (Product Nat)
  Monoid-Product-Nat .mempty = Product: 1

  Monoid-Product-Int : Monoid (Product Int)
  Monoid-Product-Int .mempty = Product: 1

  Functor-Product : Functor Product
  Functor-Product .map f = Product: <<< f <<< getProduct

  Applicative-Product : Applicative Product
  Applicative-Product .pure = Product:
  Applicative-Product ._<*>_ (Product: f) (Product: x) = Product: (f x)

  Monad-Product : Monad Product
  Monad-Product ._>>=_ (Product: x) k = k x

  Show-Product : {{_ : Show a}} -> Show (Product a)
  Show-Product .showsPrec d (Product: x) = showParen (d > appPrec)
    (showString "Show: " <<< showsPrec appPrec+1 x)
