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
    a : Type
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
  Functor-Compose .map f x = Compose: (map (map f) (getCompose x))

  Applicative-Compose : {{Applicative f}} -> {{Applicative g}}
    -> Applicative (Compose f g)
  Applicative-Compose .pure x = Compose: (pure (pure x))
  Applicative-Compose ._<*>_ f x =
    Compose: (| _<*>_ (getCompose f) (getCompose x) |)

  Foldable-Compose : {{Foldable f}} -> {{Foldable g}}
    -> Foldable (Compose f g)
  Foldable-Compose .foldr f z x = foldr (flip (foldr f)) z (getCompose x)

  Traversable-Compose : {{Traversable f}} -> {{Traversable g}}
    -> Traversable (Compose f g)
  Traversable-Compose .traverse f x =
    (| Compose: (traverse (traverse f) (getCompose x)) |)

  Alternative-Compose : {{Alternative f}} -> {{Applicative g}}
    -> Alternative (Compose f g)
  Alternative-Compose .empty = Compose: empty
  Alternative-Compose ._<|>_ l r =
    Compose: (getCompose l <|> getCompose r)
