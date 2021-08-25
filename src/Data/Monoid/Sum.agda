{-# OPTIONS --type-in-type #-}

module Data.Monoid.Sum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Int as Int using ()
open import Data.Nat as Nat using ()
open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Sum
-------------------------------------------------------------------------------

-- For additive semigroups, monoids, etc.
record Sum (a : Type) : Type where
  constructor Sum:
  field getSum : a

open Sum public

instance
  Semigroup-Sum-Nat : Semigroup (Sum Nat)
  Semigroup-Sum-Nat ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  Semigroup-Sum-Int : Semigroup (Sum Int)
  Semigroup-Sum-Int ._<>_ (Sum: m) (Sum: n) = Sum: (m + n)

  Monoid-Sum-Nat : Monoid (Sum Nat)
  Monoid-Sum-Nat .neutral = Sum: 0

  Monoid-Sum-Int : Monoid (Sum Int)
  Monoid-Sum-Int .neutral = Sum: 0

  Functor-Sum : Functor Sum
  Functor-Sum .map f = Sum: <<< f <<< getSum

  Applicative-Sum : Applicative Sum
  Applicative-Sum .pure = Sum:
  Applicative-Sum ._<*>_ (Sum: f) (Sum: x) = Sum: (f x)

  Monad-Sum : Monad Sum
  Monad-Sum ._>>=_ (Sum: x) k = k x

  Show-Sum : {{Show a}} -> Show (Sum a)
  Show-Sum .showsPrec d (Sum: x) = showParen (d > appPrec)
    (showString "Sum: " <<< showsPrec appPrec+1 x)
