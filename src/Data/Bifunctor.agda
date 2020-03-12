{-# OPTIONS --type-in-type #-}

module Data.Bifunctor where

open import Data.Pair
open import Data.Either
open import Data.Functor.Const
open import Prelude

record BifunctorOf (B C D : Category) (F : ob B -> ob C -> ob D) : Set where
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
    Functor:Bifunctor : FunctorOf (B * C) D (uncurry F)
    Functor:Bifunctor .map = uncurry bimap

open BifunctorOf {{...}} public

-- This case is so common, it deserves this abbreviation.
Bifunctor = BifunctorOf Sets Sets Sets

instance
  Bifunctor:Const : Bifunctor Const
  Bifunctor:Const .bimap f g = \ where
    (Const: x) -> Const: (f x)

  Bifunctor:Pair : Bifunctor Pair
  Bifunctor:Pair .bimap f g = cross f g

  Bifunctor:Either : Bifunctor Either
  Bifunctor:Either .bimap f g = plus f g
