module Data.Monoid.All where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- All
-------------------------------------------------------------------------------

-- Bool monoid where x <> y = x && y.
record All : Set where
  constructor anAll
  field getAll : Bool

open All public

instance
  Semigroup-All : Semigroup All
  Semigroup-All ._<>_ x y = anAll (getAll x && getAll y)

  Monoid-All : Monoid All
  Monoid-All .mempty = anAll true

  Show-All : Show All
  Show-All .showsPrec prec x = showParen (prec > appPrec) $
    showString "anAll " <<< showsPrec appPrec+1 (getAll x)
