module Data.Profunctor.Closed where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Profunctor

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
-------------------------------------------------------------------------------
-- Closed
-------------------------------------------------------------------------------

record Closed (p : Type -> Type -> Type) : Type where
  field
    overlap {{Profunctor-super}} : Profunctor p
    closed : p a b -> p (c -> a) (c -> b)

  curry : p (Tuple a b) c -> p a (b -> c)
  curry = dimap _,_ id <<< closed

open Closed {{...}} public