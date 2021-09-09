{-# OPTIONS --type-in-type #-}

module Data.Semigroup.Min where

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
-- Min
-------------------------------------------------------------------------------

-- For semigroups, monoids, etc. where x <> y = min x y
record Min (a : Set) : Set where
  constructor toMin
  field getMin : a

open Min public

instance
  Semigroup-Min : {{Ord a}} -> Semigroup (Min a)
  Semigroup-Min ._<>_ (toMin x) (toMin y) = toMin (min x y)

  Functor-Min : Functor Min
  Functor-Min .map f = toMin <<< f <<< getMin

  Applicative-Min : Applicative Min
  Applicative-Min .pure = toMin
  Applicative-Min ._<*>_ (toMin f) (toMin x) = toMin (f x)

  Monad-Min : Monad Min
  Monad-Min ._>>=_ (toMin x) k = k x

  Show-Min : {{Show a}} -> Show (Min a)
  Show-Min .showsPrec d (toMin x) = showParen (d > appPrec)
    (showString "toMin " <<< showsPrec appPrec+1 x)
