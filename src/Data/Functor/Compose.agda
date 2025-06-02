module Data.Functor.Compose where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Foldable
open import Data.Functor.Contravariant
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
  constructor asCompose
  field getCompose : f (g a)

open Compose public

instance
  Functor-Compose : {{Functor f}} -> {{Functor g}}
    -> Functor (Compose f g)
  Functor-Compose .map f x = asCompose (map (map f) (getCompose x))

  Contravariant-Compose : {{Functor f}} -> {{Contravariant g}}
    -> Contravariant (Compose f g)
  Contravariant-Compose .cmap f x = asCompose (map (cmap f) (getCompose x))

  Applicative-Compose : {{Applicative f}} -> {{Applicative g}}
    -> Applicative (Compose f g)
  Applicative-Compose .pure x = asCompose (pure (pure x))
  Applicative-Compose ._<*>_ f x =
    asCompose (| getCompose f <*> getCompose x |)

  Foldable-Compose : {{Foldable f}} -> {{Foldable g}}
    -> Foldable (Compose f g)
  Foldable-Compose .foldMap f x =
    foldMap (foldMap f) (getCompose x)

  Traversable-Compose : {{Traversable f}} -> {{Traversable g}}
    -> Traversable (Compose f g)
  Traversable-Compose .traverse f x =
    (| asCompose (traverse (traverse f) (getCompose x)) |)

  Alternative-Compose : {{Alternative f}} -> {{Applicative g}}
    -> Alternative (Compose f g)
  Alternative-Compose .azero = asCompose azero
  Alternative-Compose ._<|>_ l r =
    asCompose (getCompose l <|> getCompose r)
