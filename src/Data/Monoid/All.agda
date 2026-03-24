module Data.Monoid.All where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Show as Show using (Show; show; showsPrec)
open import Data.Show.Instances using (Show-Bool)

-------------------------------------------------------------------------------
-- All
-------------------------------------------------------------------------------

-- Bool monoid where x <> y = x && y.
record All : Type where
  constructor asAll
  field getAll : Bool

open All public

instance
  Semigroup-All : Semigroup All
  Semigroup-All ._<>_ x y = asAll (getAll x && getAll y)

  Monoid-All : Monoid All
  Monoid-All .mempty = asAll true

  Show-All : Show All
  Show-All .show = Show.showDefault
  Show-All .showsPrec prec (asAll x) =
    Show.showsUnaryWith showsPrec "asAll" prec x
