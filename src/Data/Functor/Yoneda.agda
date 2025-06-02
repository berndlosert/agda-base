module Data.Functor.Yoneda where

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
-- Yoneda
-------------------------------------------------------------------------------

record Yoneda (f : Type -> Type) (a : Type) : Type where
  constructor asYoneda
  field runYoneda : (a -> b) -> f b

open Yoneda public

liftYoneda : {{Functor f}} -> f a -> Yoneda f a
liftYoneda x = asYoneda \ f -> map f x

lowerYoneda : Yoneda f a -> f a
lowerYoneda y = runYoneda y id

instance
  Functor-Yoneda : Functor (Yoneda f)
  Functor-Yoneda .map f y = asYoneda \ g -> runYoneda y (g <<< f)
