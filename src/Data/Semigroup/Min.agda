{-# OPTIONS --type-in-type #-}

module Data.Semigroup.Min where

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
-- Min
-------------------------------------------------------------------------------

-- For semigroups, monoids, etc. where x <> y = min x y
record Min (a : Set) : Set where
  constructor Min:
  field getMin : a

open Min public

instance
  Semigroup-Min : {{_ : Ord a}} -> Semigroup (Min a)
  Semigroup-Min ._<>_ (Min: x) (Min: y) = Min: (min x y)

  Functor-Min : Functor Min
  Functor-Min .map f = Min: <<< f <<< getMin

  Applicative-Min : Applicative Min
  Applicative-Min .pure = Min:
  Applicative-Min ._<*>_ (Min: f) (Min: x) = Min: (f x)

  Monad-Min : Monad Min
  Monad-Min ._>>=_ (Min: x) k = k x

  Show-Min : {{_ : Show a}} -> Show (Min a)
  Show-Min .showsPrec d (Min: x) = showParen (d > appPrec)
    (showString "Min: " <<< showsPrec appPrec+1 x)
