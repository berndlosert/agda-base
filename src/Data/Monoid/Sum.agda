module Data.Monoid.Sum where

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
-- Sum
-------------------------------------------------------------------------------

-- For additive semigroups, monoids, etc.
record Sum (a : Type) : Type where
  constructor asSum
  field getSum : a

open Sum public

instance
  Eq-Sum : {{Eq a}} -> Eq (Sum a)
  Eq-Sum ._==_ x y = getSum x == getSum y

  Ord-Sum : {{Ord a}} -> Ord (Sum a)
  Ord-Sum ._<_ x y = getSum x < getSum y
  
  Semigroup-Sum-Nat : Semigroup (Sum Nat)
  Semigroup-Sum-Nat ._<>_ x y = asSum (getSum x + getSum y)

  Monoid-Sum-Nat : Monoid (Sum Nat)
  Monoid-Sum-Nat .mempty = asSum 0

  Semigroup-Sum-Nat1 : Semigroup (Sum Nat1)
  Semigroup-Sum-Nat1 ._<>_ (asSum m) (asSum n) = asSum (m + n)

  Semigroup-Sum-Int : Semigroup (Sum Int)
  Semigroup-Sum-Int ._<>_ x y = asSum (getSum x + getSum y)

  Monoid-Sum-Int : Monoid (Sum Int)
  Monoid-Sum-Int .mempty = asSum 0

  Semigroup-Sum-Float : Semigroup (Sum Float)
  Semigroup-Sum-Float ._<>_ x y = asSum (getSum x + getSum y)

  Monoid-Sum-Float : Monoid (Sum Float)
  Monoid-Sum-Float .mempty = asSum 0

  Functor-Sum : Functor Sum
  Functor-Sum .map f x = asSum (f (getSum x))

  Applicative-Sum : Applicative Sum
  Applicative-Sum .pure = asSum
  Applicative-Sum ._<*>_ f x = asSum (getSum f (getSum x))

  Monad-Sum : Monad Sum
  Monad-Sum ._>>=_ (asSum x) k = k x

  Show-Sum : {{Show a}} -> Show (Sum a)
  Show-Sum .show = showDefault
  Show-Sum .showsPrec prec (asSum x) =
    showsUnaryWith showsPrec "asSum" prec x