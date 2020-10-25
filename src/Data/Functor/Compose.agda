{-# OPTIONS --type-in-type #-}

module Data.Functor.Compose where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    f g : Set -> Set

-------------------------------------------------------------------------------
-- Compose
-------------------------------------------------------------------------------

record Compose (f g : Set -> Set) (a : Set) : Set where
  constructor Compose:
  field getCompose : f (g a)

open Compose public

instance
  Functor-Compose : {{_ : Functor f}} {{_ : Functor g}}
    -> Functor (Compose f g)
  Functor-Compose .map f (Compose: x) = Compose: (map (map f) x)

  Applicative-Compose : {{_ : Applicative f}} {{_ : Applicative g}}
    -> Applicative (Compose f g)
  Applicative-Compose .pure x = Compose: (pure (pure x))
  Applicative-Compose ._<*>_ (Compose: f) (Compose: x) =
    Compose: (| _<*>_ f x |)

  Foldable-Compose : {{_ : Foldable f}} {{_ : Foldable g}}
    -> Foldable (Compose f g)
  Foldable-Compose .foldMap f (Compose: x) = foldMap (foldMap f) x

  Traversable-Compose : {{_ : Traversable f}} {{_ : Traversable g}}
    -> Traversable (Compose f g)
  Traversable-Compose .traverse f (Compose: x) =
    (| Compose: (traverse (traverse f) x) |)

  Alternative-Compose : {{_ : Alternative f}} {{_ : Applicative g}}
    -> Alternative (Compose f g)
  Alternative-Compose .empty = Compose: empty
  Alternative-Compose ._<|>_ (Compose: x) (Compose: y) =
    Compose: (x <|> y)
