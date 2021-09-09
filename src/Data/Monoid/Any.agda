{-# OPTIONS --type-in-type #-}

module Data.Monoid.Any where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

-------------------------------------------------------------------------------
-- Any
-------------------------------------------------------------------------------

-- Bool monoid where x <> y = x || y.
record Any : Set where
  constructor toAny
  field getAny : Bool

open Any public

instance
  Semigroup-Any : Semigroup Any
  Semigroup-Any ._<>_ (toAny x) (toAny y) = toAny (x || y)

  Monoid-Any : Monoid Any
  Monoid-Any .neutral = toAny false

  Show-Any : Show Any
  Show-Any .showsPrec d (toAny x) = showParen (d > appPrec)
    (showString "toAny " <<< showsPrec appPrec+1 x)
