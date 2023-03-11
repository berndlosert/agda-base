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
    a b : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Representable
-------------------------------------------------------------------------------

record Representable (f : Set -> Set): Set where
  field
    overlap {{Super-functor}} : Functor f
    Rep : Set 
    tabulate : (Rep -> a) -> f a
    index : f a -> Rep -> a

open Representable {{...}} hiding (Rep) public

Rep : (f : Set -> Set) -> {{Representable f}} -> Set
Rep f {{prf}} = Representable.Rep prf
