module Data.Semigroup.FromMaybeM where

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
-- FromMaybeMM
-------------------------------------------------------------------------------

record FromMaybeM (m : Type -> Type) (a : Type) : Type where
  constructor asFromMaybeM
  field appFromMaybeM : Maybe a -> m a

open FromMaybeM public

instance
  Semigroup-FromMaybeM : {{Monad m}} -> Semigroup (FromMaybeM m a)
  Semigroup-FromMaybeM ._<>_ g f = 
    asFromMaybeM (appFromMaybeM g <=< (pure <<< just) <=< appFromMaybeM f)
