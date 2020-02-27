{-# OPTIONS --type-in-type #-}

module Data.Bifunctor where

open import Prelude

-- Programmer-friendly definition of set-valued bifunctors.
Bifunctor : (C D : Category) -> (ob C -> ob D -> Set) -> Set
Bifunctor C D P = Functor (C * D) Sets (uncurry P)

-- Convenient shorthand for endobifunctors.
Endobifunctor : (C : Category) -> (ob C -> ob C -> Set) -> Set
Endobifunctor C = Bifunctor C C

-- Some useful bifunctor instances.
open import Data.Pair
open import Data.Either

instance
  Endobifunctor:const : Endobifunctor Sets const
  Endobifunctor:const .map (Pair: f g) = f

  Endobifunctor:Tuple : Endobifunctor Sets _*_
  Endobifunctor:Tuple .map (Pair: f g) = cross f g

  Endobifunctor:Either : Endobifunctor Sets _+_
  Endobifunctor:Either .map (Pair: f g) = plus f g
