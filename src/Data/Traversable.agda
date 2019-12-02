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
    sequence : {F : Set -> Set} {{_ : Applicative F}} {X : Set}
      -> T (F X) -> F (T X)

  private
    variable
     F : Set -> Set 
     X Y : Set

  traverse : {{_ : Applicative F}} -> (X -> F Y) -> T X -> F (T Y)
  traverse f = map f >>> sequence  

  for : {{_ : Applicative F}} -> T X -> (X -> F Y) -> F (T Y)
  for = flip traverse

open Traversable {{...}} public
