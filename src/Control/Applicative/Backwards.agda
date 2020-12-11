{-# OPTIONS --type-in-type #-}

module Control.Applicative.Backwards where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Backwards
-------------------------------------------------------------------------------

record Backwards (f : Set -> Set) (a : Set) : Set where
  constructor Backwards:
  field forwards : f a

open Backwards public

instance
  Functor-Backwards : {{_ : Functor f}} -> Functor (Backwards f)
  Functor-Backwards .map f (Backwards: x) = Backwards: (map f x)

  Applicative-Backwards : {{_ : Applicative f}} -> Applicative (Backwards f)
  Applicative-Backwards .pure x = Backwards: (pure x)
  Applicative-Backwards ._<*>_ (Backwards: f) (Backwards: x) =
    Backwards: (| _#_ x f |)
