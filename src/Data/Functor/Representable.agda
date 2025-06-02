module Data.Functor.Representable where

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
    f : Type -> Type

-------------------------------------------------------------------------------
-- Representable
-------------------------------------------------------------------------------

record Representable (f : Type -> Type): Type where
  field
    overlap {{Super-functor}} : Functor f
    Rep : Type 
    tabulate : (Rep -> a) -> f a
    index : f a -> Rep -> a

open Representable {{...}} hiding (Rep) public

Rep : (f : Type -> Type) -> {{Representable f}} -> Type
Rep f {{prf}} = Representable.Rep prf
