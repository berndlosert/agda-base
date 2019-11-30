{-# OPTIONS --type-in-type #-}

module Data.Semigroup where

-- A semigroup is a type equipped with an associative binary operation.
record Semigroup (X : Set) : Set where
  constructor Semigroup:
  infixr 6 _<>_
  field _<>_ : X → X → X

open Semigroup {{...}} public 

instance
  -- Void forms the empty semigroup.
  open import Data.Void
  Semigroup:Void : Semigroup Void
  Semigroup:Void = Semigroup: \ () 

  -- Unit forms a one-element semigroup.
  open import Data.Unit
  Semigroup:Unit : Semigroup Unit
  Semigroup:Unit = Semigroup: \ _ _ → tt

-- Endofunctions form a semigroup with respect to _<<<_, but also with
-- respect to _>>>_. We use _<<<_ since this is traditionally what we
-- mean by function composition.
open import Data.Function
Semigroup:<<< : {X : Set} → Semigroup (X → X)
Semigroup:<<< = Semigroup: _<<<_

-- Functions of the form X → Y, where Y forms a semigroup are also
-- a semigroup.
Semigroup:Function : {X Y : Set} {{_ : Semigroup Y}} → Semigroup (X → Y) 
Semigroup:Function = Semigroup: \ f g x → f x <> g x 
