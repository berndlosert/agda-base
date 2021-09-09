{-# OPTIONS --type-in-type #-}

module Data.Monoid.Sum where

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
-- Sum
-------------------------------------------------------------------------------

-- For additive semigroups, monoids, etc.
record Sum (a : Set) : Set where
  constructor toSum
  field getSum : a

open Sum public

instance
  Semigroup-Sum-Nat : Semigroup (Sum Nat)
  Semigroup-Sum-Nat ._<>_ (toSum m) (toSum n) = toSum (m + n)

  Semigroup-Sum-Int : Semigroup (Sum Int)
  Semigroup-Sum-Int ._<>_ (toSum m) (toSum n) = toSum (m + n)

  Monoid-Sum-Nat : Monoid (Sum Nat)
  Monoid-Sum-Nat .neutral = toSum 0

  Monoid-Sum-Int : Monoid (Sum Int)
  Monoid-Sum-Int .neutral = toSum 0

  Functor-Sum : Functor Sum
  Functor-Sum .map f = toSum <<< f <<< getSum

  Applicative-Sum : Applicative Sum
  Applicative-Sum .pure = toSum
  Applicative-Sum ._<*>_ (toSum f) (toSum x) = toSum (f x)

  Monad-Sum : Monad Sum
  Monad-Sum ._>>=_ (toSum x) k = k x

  Show-Sum : {{Show a}} -> Show (Sum a)
  Show-Sum .showsPrec d (toSum x) = showParen (d > appPrec)
    (showString "toSum " <<< showsPrec appPrec+1 x)
