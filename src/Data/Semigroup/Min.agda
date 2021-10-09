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
  constructor toMin
  field getMin : a

open Min public

instance
  Semigroup-Min : {{Ord a}} -> Semigroup (Min a)
  Semigroup-Min ._<>_ x y = toMin $ min (getMin x) (getMin y)

  Functor-Min : Functor Min
  Functor-Min .map f = toMin <<< f <<< getMin

  Applicative-Min : Applicative Min
  Applicative-Min .pure = toMin
  Applicative-Min ._<*>_ f x = toMin $ (getMin f) (getMin x)

  Monad-Min : Monad Min
  Monad-Min ._>>=_ m k = k (getMin m)

  Show-Min : {{Show a}} -> Show (Min a)
  Show-Min .showsPrec d x = showParen (d > appPrec) $
    showString "toMin " <<< showsPrec appPrec+1 (getMin x)
