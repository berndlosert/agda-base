module Data.Monoid.EndoM where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type
    m : Type -> Type

-------------------------------------------------------------------------------
-- EndoM
-------------------------------------------------------------------------------

record EndoM (m : Type -> Type) (a : Type) : Type where
  constructor asEndoM
  field appEndoM : a -> m a

open EndoM public

instance
  Semigroup-EndoM : {{Monad m}} -> Semigroup (EndoM m a)
  Semigroup-EndoM ._<>_ g f = asEndoM (appEndoM g <=< appEndoM f)

  Monoid-EndoM : {{Monad m}} -> Monoid (EndoM m a)
  Monoid-EndoM .mempty = asEndoM pure
