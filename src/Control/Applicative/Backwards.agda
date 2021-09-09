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
  constructor toBackwards
  field forwards : f a

open Backwards public

instance
  Functor-Backwards : {{Functor f}} -> Functor (Backwards f)
  Functor-Backwards .map f (toBackwards x) = toBackwards (map f x)

  Applicative-Backwards : {{Applicative f}} -> Applicative (Backwards f)
  Applicative-Backwards .pure x = toBackwards (pure x)
  Applicative-Backwards ._<*>_ (toBackwards f) (toBackwards x) =
    toBackwards (| _#_ x f |)
