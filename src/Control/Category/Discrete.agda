{-# OPTIONS --type-in-type #-}

module Control.Category.Discrete where

open import Prelude

-- A discrete category is one having only identity morphisms. Any type X can be
-- viewed as a discrete category Discrete X.
Discrete : Set -> Category
Discrete X = record {
    ob = X;
    hom = _===_;
    _<<<_ = \ { refl refl -> refl };
    id = refl
  }

-- These are the most important discrete categories.
instance
  Zero = Discrete Void
  One = Discrete Unit
  Two = Discrete Bool
