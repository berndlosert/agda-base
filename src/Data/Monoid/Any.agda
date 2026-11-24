module Data.Monoid.Any where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Data.Monoid using (Monoid; mempty)
open import Data.Semigroup using (Semigroup; _<>_)
open import Data.Show as Show using (Show; show; showsPrec)
open import Data.Show.Instances using (Show-Bool)
open import Prelude

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
  Show-Any .show = Show.showDefault
  Show-Any .showsPrec prec (asAny x) = Show.showsUnaryWith showsPrec "asAny" prec x
