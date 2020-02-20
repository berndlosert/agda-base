{-# OPTIONS --type-in-type #-}

module Control.Alternative where

open import Control.Applicative public
open import Data.Bool
open import Data.Unit

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
guard : forall {F} {{_ : Alternative F}} -> Bool -> F Unit
guard true = pure tt
guard false = empty
