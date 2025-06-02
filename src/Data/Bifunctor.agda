module Data.Bifunctor where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d : Type

-------------------------------------------------------------------------------
-- Bifunctor
-------------------------------------------------------------------------------

record Bifunctor (p : Type -> Type -> Type) : Type where
  field
    overlap {{Functor-super}} : Functor (p a)
    lmap : (a -> b) -> p a c -> p b c

  bimap : (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = lmap f <<< map g

open Bifunctor {{...}} public

instance
  Bifunctor-Const : Bifunctor Const
  Bifunctor-Const .lmap f x = asConst (f (getConst x))

  Bifunctor-Either : Bifunctor Either
  Bifunctor-Either .lmap f = either (left <<< f) right

  Bifunctor-Tuple : Bifunctor Tuple
  Bifunctor-Tuple .lmap f (x , y) = (f x , y)