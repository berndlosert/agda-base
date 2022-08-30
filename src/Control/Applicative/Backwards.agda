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
  constructor asBackwards
  field forwards : f a

open Backwards public

instance
  Functor-Backwards : {{Functor f}} -> Functor (Backwards f)
  Functor-Backwards .map f (asBackwards x) = asBackwards (map f x)

  Applicative-Backwards : {{Applicative f}} -> Applicative (Backwards f)
  Applicative-Backwards .pure x = asBackwards (pure x)
  Applicative-Backwards ._<*>_ (asBackwards f) (asBackwards x) =
    asBackwards (| x # f |)
