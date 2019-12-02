*************************
Control.Category.Discrete
*************************
.

  {-# OPTIONS --type-in-type #-}

  module Control.Category.Discrete where

A discrete category is one having only identity morphisms. Any type X can be
viewed as a discrete category Discrete X.

  open import Control.Category
  open import Data.Eq

  Discrete : Set -> Category
  Discrete X = record {
      ob = X;
      hom = _≡_;
      _<<<_ = \ { refl refl -> refl };
      id = refl
    }

These are the most important discrete categories.

  open import Data.Bool
  open import Data.Unit
  open import Data.Void

  instance
    Zero = Discrete Void
    One = Discrete Unit
    Two = Discrete Bool
