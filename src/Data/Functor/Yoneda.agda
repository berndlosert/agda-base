module Data.Functor.Yoneda where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Constrained

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set
    c f : Set -> Set

-------------------------------------------------------------------------------
-- Yoneda
-------------------------------------------------------------------------------

-- Constrained version of Yoneda. Taken from "The Constrained-Monad Problem".
record Yoneda (c f : Set -> Set) (a : Set) : Set where
  constructor asYoneda
  field runYoneda : forall {b} -> {{c b}} -> (a -> b) -> f b

open Yoneda public

liftYoneda : {{ConstrainedFunctor c f}} -> f a -> Yoneda c f a
liftYoneda x = asYoneda \ f -> mapCF f x

lowerYoneda : {{c a}} -> Yoneda c f a -> f a
lowerYoneda y = runYoneda y id

instance
  Functor-Yoneda : Functor (Yoneda c f)
  Functor-Yoneda .map f y = asYoneda \ g -> runYoneda y (g <<< f)
