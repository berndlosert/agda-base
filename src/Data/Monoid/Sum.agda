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
    a : Set

-------------------------------------------------------------------------------
-- Sum
-------------------------------------------------------------------------------

-- For additive semigroups, monoids, etc.
record Sum (a : Set) : Set where
  constructor asSum
  field getSum : a

open Sum public

instance
  Coercible-from-Sum : Coercible (Sum a) a
  Coercible-from-Sum = coercible

  Coercible-to-Sum : Coercible a (Sum a)
  Coercible-to-Sum = coercible

  Semigroup-Sum-Num : {{Num a}} -> Semigroup (Sum a)
  Semigroup-Sum-Num {a} ._<>_ x y = asSum (getSum x + getSum y)

  Monoid-Sum-Num : {{Num a}} -> Monoid (Sum a)
  Monoid-Sum-Num .mempty = asSum 0

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
