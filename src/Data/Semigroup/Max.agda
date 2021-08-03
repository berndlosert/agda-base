{-# OPTIONS --type-in-type #-}

module Data.Semigroup.Max where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Max
-------------------------------------------------------------------------------

-- For semigroups, monoids, etc. where x <> y = max x y
record Max (a : Type) : Type where
  constructor Max:
  field getMax : a

open Max public

instance
  Semigroup-Max : {{Ord a}} -> Semigroup (Max a)
  Semigroup-Max ._<>_ (Max: x) (Max: y) = Max: (max x y)

  Functor-Max : Functor Max
  Functor-Max .map f = Max: <<< f <<< getMax

  Applicative-Max : Applicative Max
  Applicative-Max .pure = Max:
  Applicative-Max ._<*>_ (Max: f) (Max: x) = Max: (f x)

  Monad-Max : Monad Max
  Monad-Max ._>>=_ (Max: x) k = k x

  Show-Max : {{Show a}} -> Show (Max a)
  Show-Max .showsPrec d (Max: x) = showParen (d > appPrec)
    (showString "Max: " <<< showsPrec appPrec+1 x)
