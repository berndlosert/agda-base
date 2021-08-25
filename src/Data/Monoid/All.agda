{-# OPTIONS --type-in-type #-}

module Data.Monoid.All where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

-------------------------------------------------------------------------------
-- All
-------------------------------------------------------------------------------

-- Bool monoid where x <> y = x && y.
record All : Type where
  constructor All:
  field getAll : Bool

open All public

instance
  Semigroup-All : Semigroup All
  Semigroup-All ._<>_ (All: x) (All: y) = All: (x && y)

  Monoid-All : Monoid All
  Monoid-All .neutral = All: True

  Show-All : Show All
  Show-All .showsPrec d (All: x) = showParen (d > appPrec)
    (showString "Show: " <<< showsPrec appPrec+1 x)
