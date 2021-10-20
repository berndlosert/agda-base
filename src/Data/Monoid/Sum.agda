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
  constructor aSum
  field getSum : a

open Sum public

instance
  Semigroup-Sum-Nat : Semigroup (Sum Nat)
  Semigroup-Sum-Nat ._<>_ m n = aSum (getSum m + getSum n)

  Semigroup-Sum-Int : Semigroup (Sum Int)
  Semigroup-Sum-Int ._<>_ m n = aSum (getSum m + getSum n)

  Monoid-Sum-Nat : Monoid (Sum Nat)
  Monoid-Sum-Nat .mempty = aSum 0

  Monoid-Sum-Int : Monoid (Sum Int)
  Monoid-Sum-Int .mempty = aSum 0

  Functor-Sum : Functor Sum
  Functor-Sum .map f = aSum <<< f <<< getSum

  Applicative-Sum : Applicative Sum
  Applicative-Sum .pure = aSum
  Applicative-Sum ._<*>_ f x = aSum $ (getSum f) (getSum x)

  Monad-Sum : Monad Sum
  Monad-Sum ._>>=_ (aSum x) k = k x

  Show-Sum : {{Show a}} -> Show (Sum a)
  Show-Sum .showsPrec prec x = showParen (prec > appPrec) $
    showString "aSum " <<< showsPrec appPrec+1 (getSum x)
