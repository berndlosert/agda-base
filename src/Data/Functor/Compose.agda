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

abstract
  Compose : (f g : Type -> Type) (a : Type) -> Type
  Compose f g a = f (g a)

  mkCompose : f (g a) -> Compose f g a
  mkCompose = id

  getCompose : Compose f g a -> f (g a)
  getCompose = id

instance
  Functor-Compose : {{Functor f}} -> {{Functor g}}
    -> Functor (Compose f g)
  Functor-Compose .map f x = mkCompose (map (map f) (getCompose x))

  Applicative-Compose : {{Applicative f}} -> {{Applicative g}}
    -> Applicative (Compose f g)
  Applicative-Compose .pure x = mkCompose (pure (pure x))
  Applicative-Compose ._<*>_ f x =
    mkCompose (| _<*>_ (getCompose f) (getCompose x) |)

  Foldable-Compose : {{Foldable f}} -> {{Foldable g}}
    -> Foldable (Compose f g)
  Foldable-Compose .foldr f z x = foldr (flip (foldr f)) z (getCompose x)

  Traversable-Compose : {{Traversable f}} -> {{Traversable g}}
    -> Traversable (Compose f g)
  Traversable-Compose .traverse f x =
    (| mkCompose (traverse (traverse f) (getCompose x)) |)

  Alternative-Compose : {{Alternative f}} -> {{Applicative g}}
    -> Alternative (Compose f g)
  Alternative-Compose .empty = mkCompose empty
  Alternative-Compose ._<|>_ l r =
    mkCompose (getCompose l <|> getCompose r)
