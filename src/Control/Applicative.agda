{-# OPTIONS --type-in-type #-}

module Control.Applicative where

-- Definition of applicative functors.

open import Data.Function
open import Data.Functor public

record Applicative (F : Set -> Set) : Set where
  constructor Applicative:
  infixl 24 _<*>_ _*>_ _<*_
  field
    overlap {{Functor:Applicative}} : Endofunctor Sets F
    _<*>_ : forall {X Y} -> F (X -> Y) -> F X -> F Y
    pure : forall {X} -> X -> F X

  -- Generalization of flip const.

  _*>_ : forall {X Y} -> F X -> F Y -> F Y
  x *> y = (| (flip const) x y |)

  -- Generalization of const.

  _<*_ : forall {X Y} -> F X -> F Y -> F X
  x <* y = (| const x y |)

open Applicative {{...}} public

-- Every monad of type Set -> Set is an applicative with unit = return
-- and _<*>_ = ap, where ap defined as follows:

open import Control.Monad

ap : forall {F X Y} {{_ : Monad Sets F}}
  -> F (X -> Y) -> F X -> F Y
ap fs xs = do
  f <- fs
  x <- xs
  return (f x)
