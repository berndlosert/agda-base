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
record Any : Type where
  constructor Any:
  field getAny : Bool

open Any public

instance
  Semigroup-Any : Semigroup Any
  Semigroup-Any ._<>_ (Any: x) (Any: y) = Any: (x || y)

  Monoid-Any : Monoid Any
  Monoid-Any .neutral = Any: False

  Show-Any : Show Any
  Show-Any .showsPrec d (Any: x) = showParen (d > appPrec)
    (showString "Any: " <<< showsPrec appPrec+1 x)
