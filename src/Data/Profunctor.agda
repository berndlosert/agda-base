{-# OPTIONS --type-in-type #-}

module Data.Profunctor where

open import Prelude

record Profunctor (C D : Category) (P : ob D -> ob C -> Set) : Set where
  constructor Profunctor:
  field
    dimap : forall {W X Y Z}
      -> hom D W X -> hom C Y Z
      -> P X Y -> P W Z

  lmap : forall {W X Y} -> hom D W X -> P X Y -> P W Y
  lmap f = dimap f id
    where instance _ = C

  rmap : forall {X Y Z} -> hom C Y Z -> P X Y -> P X Z
  rmap g = dimap id g
    where instance _ = D

  instance
    Functor:Profunctor : Functor (Op D * C) Sets (uncurry P)
    Functor:Profunctor .map = uncurry dimap

open Profunctor {{...}} public

Endoprofunctor : (C : Category) -> (ob C -> ob C -> Set) -> Set
Endoprofunctor C = Profunctor C C

Profunctor:hom : (C : Category) -> Profunctor C C (hom C)
Profunctor:hom C .dimap f g h = f >>> h >>> g
  where instance _ = C

instance
  Profunctor:Function = Profunctor:hom Sets
