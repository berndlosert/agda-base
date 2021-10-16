{-# OPTIONS --type-in-type #-}

module Data.Functor.Compose where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    f g : Set -> Set

-------------------------------------------------------------------------------
-- Compose
-------------------------------------------------------------------------------

record Compose (f g : Set -> Set) (a : Set) : Set where
  constructor toCompose
  field getCompose : f (g a)

open Compose public

instance
  Functor-Compose : {{Functor f}} -> {{Functor g}}
    -> Functor (Compose f g)
  Functor-Compose .map f x = toCompose (map (map f) (getCompose x))

  Applicative-Compose : {{Applicative f}} -> {{Applicative g}}
    -> Applicative (Compose f g)
  Applicative-Compose .pure x = toCompose (pure (pure x))
  Applicative-Compose ._<*>_ f x =
    toCompose (| getCompose f <*> getCompose x |)

  Foldable-Compose : {{Foldable f}} -> {{Foldable g}}
    -> Foldable (Compose f g)
  Foldable-Compose .foldr step init x =
    foldr (flip (foldr step)) init (getCompose x)

  Traversable-Compose : {{Traversable f}} -> {{Traversable g}}
    -> Traversable (Compose f g)
  Traversable-Compose .traverse f x =
    (| toCompose (traverse (traverse f) (getCompose x)) |)

  Alternative-Compose : {{Alternative f}} -> {{Applicative g}}
    -> Alternative (Compose f g)
  Alternative-Compose .azero = toCompose azero
  Alternative-Compose ._<|>_ l r =
    toCompose (getCompose l <|> getCompose r)
