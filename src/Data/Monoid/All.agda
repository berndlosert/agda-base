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
  Semigroup-All ._<>_ x y = toAll (getAll x && getAll y)

  Monoid-All : Monoid All
  Monoid-All .neutral = toAll true

  Show-All : Show All
  Show-All .showsPrec d x = showParen (d > appPrec) $
    showString "toAll " <<< showsPrec appPrec+1 (getAll x)
