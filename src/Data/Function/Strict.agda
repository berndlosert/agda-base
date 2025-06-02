module Data.Function.Strict where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
      a b : Type

-------------------------------------------------------------------------------
-- Strict functions
-------------------------------------------------------------------------------

abstract
  Strict : Type -> Type -> Type
  Strict a b = a -> b

  asStrict : (a -> b) -> Strict a b
  asStrict f = f

  applyStrict : Strict a b -> a -> b
  applyStrict f x = f $! x

instance
  Semigroupoid-Strict : Semigroupoid Strict
  Semigroupoid-Strict ._<<<_ g f = asStrict \ x -> applyStrict g (applyStrict f x)

  Category-Strict : Category Strict
  Category-Strict .id = asStrict \ x -> x