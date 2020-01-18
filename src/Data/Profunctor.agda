{-# OPTIONS --type-in-type #-}

module Data.Profunctor where

-- Programmer-friendly definition of profunctors.

open import Data.Functor public
open import Data.Tuple

Profunctor : (C D : Category) -> (ob D -> ob C -> Set) -> Set
Profunctor C D P = Functor (Op D * C) Sets (uncurry P)

Endoprofunctor : (C : Category) -> (ob C -> ob C -> Set) -> Set
Endoprofunctor C = Profunctor C C

-- For every cateogry C, hom C forms a profunctor.

Profunctor:hom : (C : Category) -> Profunctor C C (hom C)
Profunctor:hom C .map (f , g) h = f >>> h >>> g
  where instance _ = C

instance
  Profunctor:Function = Profunctor:hom Sets
