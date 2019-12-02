{-# OPTIONS --type-in-type #-}

module Data.Traversable where

-- Traversable functors are characterised as those which distribute over all
-- applicative functors.

open import Control.Applicative
open import Control.Category
open import Data.Function
open import Data.Functor

record Traversable (T : Set -> Set) : Set where
  constructor Traversable:
  field
    {{instance:Functor}} : Endofunctor Sets T
    sequence : forall {F X} {{_ : Applicative F}}
      -> T (F X) -> F (T X)

  traverse : forall {F X Y} {{_ : Applicative F}}
    -> (X -> F Y) -> T X -> F (T Y)
  traverse f = map f >>> sequence

  for : forall {F X Y} {{_ : Applicative F}}
    -> T X -> (X -> F Y) -> F (T Y)
  for = flip traverse

open Traversable {{...}} public
