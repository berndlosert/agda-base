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

-- id forms an applicative functor.

Applicative:id : Applicative id
Applicative:id .Functor:Applicative = Functor:id Sets
Applicative:id ._<*>_ f x = f x
Applicative:id .pure x = x

-- For every monoid X, const X is an applicative functor.

Applicative:const : forall {X} {{_ : Monoid X}} -> Applicative (const X)
Applicative:const {X} .Functor:Applicative = Functor:const {Sets} {Sets} X
Applicative:const ._<*>_ f x = f <> x
Applicative:const .pure _ = mempty

-- An applicative functor F such that F X is a monoid for all X is called an
-- alternative functor.

record Alternative (F : Set -> Set) : Set where
  constructor Altervative:
  infixl 23 _<|>_
  field
    {{Applicative:Alternative}} : Applicative F
    _<|>_ : forall {X} -> F X -> F X -> F X
    empty : forall {X} -> F X

open Alternative {{...}} public

-- Conditional failure of Alternative computations.

open import Data.Bool
open import Data.Unit

guard : forall {F} {{_ : Alternative F}} -> Bool -> F Unit
guard true = pure tt
guard false = empty
