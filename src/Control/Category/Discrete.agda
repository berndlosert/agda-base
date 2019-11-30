{-# OPTIONS --type-in-type #-}

module Control.Category.Discrete where

open import Control.Category
open import Data.Bool
open import Data.Eq
open import Data.Product
open import Data.Unit
open import Data.Void

-- A discrete category is one having only identity morphisms. Any type X can be
-- viewed as a discrete category Discrete X.
Discrete : Set -> Category
Discrete X = record {
    ob = X;
    hom = _===_;
    _>>>_ = \ { refl refl -> refl };
    id = refl
  }

instance
  -- These are the most important discrete categories.
  Zero = Discrete Void
  One = Discrete Unit
  Two = Discrete Bool
