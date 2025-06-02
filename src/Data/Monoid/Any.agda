module Data.Monoid.Any where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Show

-------------------------------------------------------------------------------
-- Any
-------------------------------------------------------------------------------

-- Bool monoid where x <> y = x || y.
record Any : Type where
  constructor asAny
  field getAny : Bool

open Any public

instance
  Semigroup-Any : Semigroup Any
  Semigroup-Any ._<>_ x y = asAny (getAny x || getAny y)

  Monoid-Any : Monoid Any
  Monoid-Any .mempty = asAny false

  Show-Any : Show Any
  Show-Any .show = showDefault
  Show-Any .showsPrec prec (asAny x) = showsUnaryWith showsPrec "asAny" prec x
