{-# OPTIONS --type-in-type #-}

module Data.Functor.Hom where

open import Control.Category
open import Data.Functor
open import Data.Tuple

-- Hom C is the bifunctor version of hom C.
Hom : (C : Category) -> ob (Op C * C) -> Set
Hom C = uncurry (hom C)

Functor:Hom : (C : Category) -> Functor (Op C * C) Sets (Hom C)
Functor:Hom C .map (f , g) h = f >>> h >>> g
  where instance _ = C
