module Control.Monad.Constrained where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    c f m : Set -> Set
    a b : Set

-------------------------------------------------------------------------------
-- ConstrainedFunctor
-------------------------------------------------------------------------------

record ConstrainedFunctor (c f : Set -> Set) : Set where
  field conmap : {{c b}} -> (a -> b) -> f a -> f b

open ConstrainedFunctor {{...}} public

-------------------------------------------------------------------------------
-- ConstrainedManad
-------------------------------------------------------------------------------

record ConstrainedMonad (c m : Set -> Set) : Set where
  field
    overlap {{super}} : ConstrainedFunctor c m
    conbind : {{c b}} -> m a -> (a -> m b) -> m b
    conreturn : a -> m a

open ConstrainedMonad {{...}} public

-------------------------------------------------------------------------------
-- Unconstrained
-------------------------------------------------------------------------------

Unconstrained : Set -> Set
Unconstrained _ = Unit