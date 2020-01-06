{-# OPTIONS --type-in-type #-}

module Data.Semigroup where

-- A semigroup is a type equipped with an associative binary operation.

record Semigroup (X : Set) : Set where
  constructor Semigroup:
  infixr 6 _<>_
  field _<>_ : X -> X -> X

open Semigroup {{...}} public

-- Void forms the empty semigroup.

instance
  open import Data.Void
  Semigroup:Void : Semigroup Void
  Semigroup:Void = Semigroup: \ ()

-- Unit forms a one-element semigroup.

instance
  open import Data.Unit
  Semigroup:Unit : Semigroup Unit
  Semigroup:Unit = Semigroup: \ _ _ -> tt

-- For every category C and every object X : ob C, hom C X X is a semigroup
-- under composition and flipped composition.

open import Control.Category
open import Data.Tuple

Semigroup:<<< : forall C {X} -> Semigroup (hom C (X , X))
Semigroup:<<< C = Semigroup: _<<<_
  where instance _ = C

Semigroup:>>> : forall C {X} -> Semigroup (hom C (X , X))
Semigroup:>>> C = Semigroup: _>>>_
  where instance _ = C

-- Functions of the form X -> Y, where Y forms a semigroup, also
-- form a semigroup.

Semigroup:Function : {X Y : Set} {{_ : Semigroup Y}} -> Semigroup (X -> Y)
Semigroup:Function = Semigroup: \ f g x -> f x <> g x
