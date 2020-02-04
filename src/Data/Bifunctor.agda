{-# OPTIONS --type-in-type #-}

module Data.Bifunctor where

-- Programmer-friendly definition of set-valued bifunctors.

open import Data.Functor public
open import Data.Tuple

Bifunctor : (C D : Category) -> (ob C -> ob D -> Set) -> Set
Bifunctor C D P = Functor (C * D) Sets (uncurry P)

-- Convenient shorthand for endobifunctors.

Endobifunctor : (C : Category) -> (ob C -> ob C -> Set) -> Set
Endobifunctor C = Bifunctor C C

-- Some useful bifunctor instances.

open import Data.Either
open import Data.Function

instance
  Endobifunctor:const : Endobifunctor Sets const
  Endobifunctor:const .map (pair f g) = f

  Endobifunctor:Tuple : Endobifunctor Sets _*_
  Endobifunctor:Tuple .map (pair f g) = cross f g

  Endobifunctor:Either : Endobifunctor Sets _+_
  Endobifunctor:Either .map (pair f g) = plus f g
