module Data.Distributive where

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
    f g : Type -> Type

-------------------------------------------------------------------------------
-- Distributive
-------------------------------------------------------------------------------

record Distributive (g : Type -> Type) : Type where
  field
    overlap {{Functor-super}} : Functor g
    distribute : {{Functor f}} -> f (g a) -> g (f a)

  collect : {{Functor f}} -> (a -> g b) -> f a -> g (f b)
  collect f = distribute <<< map f

  cotraverse : {{Functor f}} -> (f a -> b) -> f (g a) -> g b
  cotraverse f = map f <<< distribute

open Distributive {{...}} public

instance
  Distributive-Function : Distributive (Function a)
  Distributive-Function .distribute f x = map (_$  x) f

  Distributive-Identity : Distributive Identity
  Distributive-Identity .distribute x = asIdentity (map runIdentity x)
