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
  constructor aBackwards
  field forwards : f a

open Backwards public

instance
  Functor-Backwards : {{Functor f}} -> Functor (Backwards f)
  Functor-Backwards .map f (aBackwards x) = aBackwards (map f x)

  Applicative-Backwards : {{Applicative f}} -> Applicative (Backwards f)
  Applicative-Backwards .pure x = aBackwards (pure x)
  Applicative-Backwards ._<*>_ (aBackwards f) (aBackwards x) =
    aBackwards (| x # f |)
