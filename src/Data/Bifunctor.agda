{-# OPTIONS --type-in-type #-}

module Data.Bifunctor where

open import Prelude

record Bifunctor (B C D : Category) (F : ob B -> ob C -> ob D) : Set where
  constructor Bifunctor:
  field
    bimap : forall {X X' Y Y'}
      -> hom B X Y -> hom C X' Y'
      -> hom D (F X X') (F Y Y')

  lmap : forall {X Y Z} -> hom B X Y -> hom D (F X Z) (F Y Z)
  lmap f = bimap f id
    where instance _ = C

  rmap : forall {X Y Z} -> hom C X Y -> hom D (F Z X) (F Z Y)
  rmap g = bimap id g
    where instance _ = B

  instance
    Functor:Bifunctor : Functor (B * C) D (uncurry F)
    Functor:Bifunctor .map = uncurry bimap

open Bifunctor {{...}} public

Dyadic : (C : Category) -> (ob C -> ob C -> ob C) -> Set
Dyadic C = Bifunctor C C C

open import Data.Pair
open import Data.Either

instance
  Dyadic:const : Dyadic Sets const
  Dyadic:const .bimap f g = f

  Dyadic:Tuple : Dyadic Sets _*_
  Dyadic:Tuple .bimap f g = cross f g

  Dyadic:Either : Dyadic Sets _+_
  Dyadic:Either .bimap f g = plus f g
