module Control.Semigroupoid where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Semigroupoid
-------------------------------------------------------------------------------

record Semigroupoid {k : Type} (p : k -> k -> Type) : Type where
  infixr 9 _<<<_
  field _<<<_ : {a b c : k} -> p b c -> p a b -> p a c

  infixr 9 _>>>_
  _>>>_ : {a b c : k} -> p a b -> p b c -> p a c
  _>>>_ = flip _<<<_

open Semigroupoid {{...}} public

instance
  Semigroupoid-Function : Semigroupoid Function
  Semigroupoid-Function ._<<<_ g f x = g (f x)
