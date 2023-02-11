module Data.Functor.Sum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Functor.Contravariant
open import Data.String.Show
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    f g : Set -> Set

-------------------------------------------------------------------------------
-- Sum
-------------------------------------------------------------------------------

data Sum (f g : Set -> Set) (a : Set) : Set where
  inl : f a -> Sum f g a
  inr : g a -> Sum f g a

instance
  Functor-Sum : {{Functor f}} -> {{Functor g}} -> Functor (Sum f g)
  Functor-Sum .map f = \ where
    (inl x) -> inl (map f x)
    (inr y) -> inr (map f y)

  Contravariant-Sum : {{Contravariant f}} -> {{Contravariant g}} -> Contravariant (Sum f g)
  Contravariant-Sum .cmap f = \ where
    (inl x) -> inl (cmap f x)
    (inr y) -> inr (cmap f y)

  Foldable-Sum : {{Foldable f}} -> {{Foldable g}} -> Foldable (Sum f g)
  Foldable-Sum .foldr step init = \ where
    (inl x) -> foldr step init x
    (inr y) -> foldr step init y

  Traversable-Sum : {{Traversable f}} -> {{Traversable g}} -> Traversable (Sum f g)
  Traversable-Sum .traverse f = \ where
    (inl x) -> (| inl (traverse f x) |)
    (inr y) -> (| inr (traverse f y) |)

  Show-Sum : {{Show (f a)}} -> {{Show (g a)}} -> Show (Sum f g a)
  Show-Sum .show = showDefault
  Show-Sum .showsPrec prec = \ where
    (inl x) -> showsUnaryWith showsPrec "inl" prec x
    (inr x) -> showsUnaryWith showsPrec "inr" prec x
