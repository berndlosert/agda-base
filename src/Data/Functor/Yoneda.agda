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
    a b : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Yoneda
-------------------------------------------------------------------------------

Yoneda : (Set -> Set) -> Set -> Set
Yoneda f a = forall {b} -> (a -> b) -> f b

instance
  Functor-Yoneda : Functor (Yoneda f)
  Functor-Yoneda .map f t g = t (g <<< f)

lift : {{Functor f}} -> f a -> Yoneda f a
lift y f = map f y

lower : Yoneda f a -> f a
lower t = t id
