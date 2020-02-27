{-# OPTIONS --type-in-type #-}

module Control.Comonad where

open import Prelude

-- A functor F : ob C -> ob C is a comonad when it comes with natural
-- transformations extract and coextend/duplicate obeying the comonad laws.
record Comonad (C : Category) (F : ob C -> ob C) : Set where
  constructor Comonad:
  field
    {{Functor:Comonad}} : Functor C C F
    coextend : forall {X Y} -> hom C (F X) Y -> hom C (F X) (F Y)
    extract : forall {X} -> hom C (F X) X

  duplicate : forall {X} -> hom C (F X) (F (F X))
  duplicate {X} = coextend id
    where instance _ = C

open Comonad {{...}} public

module _ {F : Set -> Set} {{_ : Comonad Sets F}} {X Y : Set} where

  infixl 1 _=>>_ _=>=_

  -- The cobind operator.
  _=>>_ : F X -> (F X -> Y) -> F Y
  x =>> f = coextend f x

  -- Cokleisli composition for comonads on Sets.
  _=>=_ : forall {Z} -> (F X -> Y) -> (F Y -> Z) -> (F X -> Z)
  f =>= g = coextend f >>> g
