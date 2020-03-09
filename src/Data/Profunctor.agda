{-# OPTIONS --type-in-type #-}

module Data.Profunctor where

open import Data.Bifunctor public
open import Prelude

Profunctor : (C D : Category) -> (ob D -> ob C -> Set) -> Set
Profunctor C D = Bifunctor (Op D) C Sets

Profunctor:hom : (C : Category) -> Profunctor C C (hom C)
Profunctor:hom C .bimap f g h = f >>> h >>> g
  where instance _ = C

instance
  Profunctor:Function = Profunctor:hom Sets
