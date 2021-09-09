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
record All : Set where
  constructor toAll
  field getAll : Bool

open All public

instance
  Semigroup-All : Semigroup All
  Semigroup-All ._<>_ (toAll x) (toAll y) = toAll (x && y)

  Monoid-All : Monoid All
  Monoid-All .neutral = toAll true

  Show-All : Show All
  Show-All .showsPrec d (toAll x) = showParen (d > appPrec)
    (showString "toAll " <<< showsPrec appPrec+1 x)
