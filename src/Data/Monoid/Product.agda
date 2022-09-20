module Data.Monoid.Product where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Builder
open import Data.String.Show

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
  constructor asProduct
  field getProduct : a

open Product public

instance
  Semigroup-Product-Nat : Semigroup (Product Nat)
  Semigroup-Product-Nat ._<>_ m n = asProduct (getProduct m * getProduct n)

  Semigroup-Product-Int : Semigroup (Product Int)
  Semigroup-Product-Int ._<>_ m n = asProduct (getProduct m * getProduct n)

  Monoid-Product-Nat : Monoid (Product Nat)
  Monoid-Product-Nat .mempty = asProduct 1

  Monoid-Product-Int : Monoid (Product Int)
  Monoid-Product-Int .mempty = asProduct 1

  Functor-Product : Functor Product
  Functor-Product .map f = asProduct <<< f <<< getProduct

  Applicative-Product : Applicative Product
  Applicative-Product .pure = asProduct
  Applicative-Product ._<*>_ f x = asProduct $ (getProduct f) (getProduct x)

  Monad-Product : Monad Product
  Monad-Product ._>>=_ (asProduct x) k = k x

  Show-Product : {{Show a}} -> Show (Product a)
  Show-Product .show = showDefault
  Show-Product .showsPrec prec x = showParen (prec > appPrec)
    ("asProduct " <> showsPrec appPrec+1 (getProduct x))
