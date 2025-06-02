module Data.Semigroup.Min where

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
-- Min
-------------------------------------------------------------------------------

-- For semigroups, monoids, etc. where x <> y = min x y
record Min (a : Type) : Type where
  constructor asMin
  field getMin : a

open Min public

instance
  Semigroup-Min : {{Ord a}} -> Semigroup (Min a)
  Semigroup-Min ._<>_ x y = asMin (min (getMin x) (getMin y))

  Functor-Min : Functor Min
  Functor-Min .map f = asMin <<< f <<< getMin

  Applicative-Min : Applicative Min
  Applicative-Min .pure = asMin
  Applicative-Min ._<*>_ f x = asMin ((getMin f) (getMin x))

  Monad-Min : Monad Min
  Monad-Min ._>>=_ m k = k (getMin m)

  Show-Min : {{Show a}} -> Show (Min a)
  Show-Min .show = showDefault
  Show-Min .showsPrec prec (asMin x) = showsUnaryWith showsPrec "min" prec x
