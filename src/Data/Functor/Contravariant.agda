module Data.Functor.Contravariant where

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
-- Contravariant
-------------------------------------------------------------------------------

record Contravariant (f : Type -> Type) : Type where
  field cmap : (a -> b) -> f b -> f a

  phantom : {{Functor f}} -> f a -> f b
  phantom x = cmap (const tt) (map (const tt) x)

open Contravariant {{...}} public

instance
  Contravariant-Const : Contravariant (Const a)
  Contravariant-Const .cmap f x = asConst (getConst x)