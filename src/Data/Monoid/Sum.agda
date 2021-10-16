{-# OPTIONS --type-in-type #-}

module Data.Monoid.Sum where

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
-- Sum
-------------------------------------------------------------------------------

-- For additive semigroups, monoids, etc.
record Sum (a : Set) : Set where
  constructor toSum
  field getSum : a

open Sum public

instance
  Semigroup-Sum-Nat : Semigroup (Sum Nat)
  Semigroup-Sum-Nat ._<>_ m n = toSum (getSum m + getSum n)

  Semigroup-Sum-Int : Semigroup (Sum Int)
  Semigroup-Sum-Int ._<>_ m n = toSum (getSum m + getSum n)

  Monoid-Sum-Nat : Monoid (Sum Nat)
  Monoid-Sum-Nat .mempty = toSum 0

  Monoid-Sum-Int : Monoid (Sum Int)
  Monoid-Sum-Int .mempty = toSum 0

  Functor-Sum : Functor Sum
  Functor-Sum .map f = toSum <<< f <<< getSum

  Applicative-Sum : Applicative Sum
  Applicative-Sum .pure = toSum
  Applicative-Sum ._<*>_ f x = toSum $ (getSum f) (getSum x)

  Monad-Sum : Monad Sum
  Monad-Sum ._>>=_ (toSum x) k = k x

  Show-Sum : {{Show a}} -> Show (Sum a)
  Show-Sum .showsPrec prec x = showParen (prec > appPrec) $
    showString "toSum " <<< showsPrec appPrec+1 (getSum x)
