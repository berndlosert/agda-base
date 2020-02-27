{-# OPTIONS --type-in-type #-}

module Data.Profunctor where

open import Prelude

-- Programmer-friendly definition of profunctors.
Profunctor : (C D : Category) -> (ob D -> ob C -> Set) -> Set
Profunctor C D P = Functor (Op D * C) Sets (uncurry P)

Endoprofunctor : (C : Category) -> (ob C -> ob C -> Set) -> Set
Endoprofunctor C = Profunctor C C

-- dimap f g is shorthand for map (Pair: f g).
dimap : forall {C D P X X' Y Y'} {{_ : Profunctor C D P}}
  -> hom (Op D) X X' -> hom C Y Y' -> P X Y -> P X' Y'
dimap f g = map (Pair: f g)

-- For every cateogry C, hom C forms a profunctor.
Profunctor:hom : (C : Category) -> Profunctor C C (hom C)
Profunctor:hom C .map (Pair: f g) h = f >>> h >>> g
  where instance _ = C

instance
  Profunctor:Function = Profunctor:hom Sets
