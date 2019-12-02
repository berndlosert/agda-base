{-# OPTIONS --type-in-type #-}

module Control.Comonad where

-- A functor F : ob C -> ob C is a comonad when it comes with two natural
-- transformations extract and duplicate obeying the comonad laws.

open import Control.Category
open import Data.Functor

record Comonad (C : Category) (F : ob C -> ob C) : Set where
  constructor Comonad:
  field
    {{instance:Functor}} : Functor C C F
    duplicate : forall {X} -> hom C (F X) (F (F X))
    extract : forall {X} -> hom C (F X) X

  extend : forall {X Y} -> hom C (F X) Y -> hom C (F X) (F Y)
  extend f = let instance _ = C in duplicate >>> map f

open Comonad {{...}} hiding (instance:Functor) public

-- Cokleisli F is the coKleisli category of a comonad F.

Cokleisli : forall {C} F {{_ : Comonad C F}} -> Category
Cokleisli {C} F = let instance _ = C in
  record {
    ob = ob C;
    hom = \ X Y -> hom C (F X) Y;
    _<<<_ = \ g f -> g <<< extend f;
    id = extract
  }

-- id is trivially a comonad.

Comonad:id : (C : Category) -> Comonad C id
Comonad:id C = let instance _ = C in
  record {
      instance:Functor = Functor:id C;
      duplicate = id;
      extract = id
  }

-- extend with the arguments swapped. Dual of _>>=_.

infixl 1 _=>>_

_=>>_ : forall {F X Y} {{_ : Comonad Sets F}}
  -> F X -> (F X -> Y) -> F Y
x =>> f = extend f x

-- Cokleisli composition for comonads on Sets.

infixl 1 _=>=_
_=>=_ : forall {F X Y Z} {{_ : Comonad Sets F}}
  -> (F X -> Y) -> (F Y -> Z) -> (F X -> Z)
f =>= g = extend f >>> g
