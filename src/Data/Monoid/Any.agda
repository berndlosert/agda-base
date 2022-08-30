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
  constructor asAny
  field getAny : Bool

open Any public

instance
  Semigroup-Any : Semigroup Any
  Semigroup-Any ._<>_ x y = asAny (getAny x || getAny y)

  Monoid-Any : Monoid Any
  Monoid-Any .mempty = asAny false

  Show-Any : Show Any
  Show-Any .showsPrec prec x = showParen (prec > appPrec) $
    showString "asAny " <<< showsPrec appPrec+1 (getAny x)
