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
    f g : Type -> Type

-------------------------------------------------------------------------------
-- Compose
-------------------------------------------------------------------------------

record Compose (f g : Type -> Type) (a : Type) : Type where
  constructor Compose:
  field getCompose : f (g a)

open Compose public

instance
  Functor-Compose : {{Functor f}} -> {{Functor g}}
    -> Functor (Compose f g)
  Functor-Compose .map f (Compose: x) = Compose: (map (map f) x)

  Applicative-Compose : {{Applicative f}} -> {{Applicative g}}
    -> Applicative (Compose f g)
  Applicative-Compose .pure x = Compose: (pure (pure x))
  Applicative-Compose ._<*>_ (Compose: f) (Compose: x) =
    Compose: (| _<*>_ f x |)

  Foldable-Compose : {{Foldable f}} -> {{Foldable g}}
    -> Foldable (Compose f g)
  Foldable-Compose .foldr f z (Compose: x) = foldr (flip (foldr f)) z x

  Traversable-Compose : {{Traversable f}} -> {{Traversable g}}
    -> Traversable (Compose f g)
  Traversable-Compose .traverse f (Compose: x) =
    (| Compose: (traverse (traverse f) x) |)

  Alternative-Compose : {{Alternative f}} -> {{Applicative g}}
    -> Alternative (Compose f g)
  Alternative-Compose .empty = Compose: empty
  Alternative-Compose ._<|>_ (Compose: x) (Compose: y) =
    Compose: (x <|> y)
