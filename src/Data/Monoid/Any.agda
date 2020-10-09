{-# OPTIONS --type-in-type #-}

module Data.Monoid.Any where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Any
-------------------------------------------------------------------------------

-- Bool monoid where x <> y = x || y.
record Any : Set where
  constructor Any:
  field getAny : Bool

open Any public

instance
  Semigroup-Any : Semigroup Any
  Semigroup-Any ._<>_ (Any: x) (Any: y) = Any: (x || y)

  Monoid-Any : Monoid Any
  Monoid-Any .mempty = Any: False

  Show-Any : {{_ : Show a}} -> Show Any
  Show-Any .showsPrec d (Any: x) = showParen (d > appPrec)
    (showString "Show: " <<< showsPrec appPrec+1 x)
