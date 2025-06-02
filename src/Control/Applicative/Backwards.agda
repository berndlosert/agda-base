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
    a b c : Type
    f t : Type -> Type

-------------------------------------------------------------------------------
-- Backwards
-------------------------------------------------------------------------------

record Backwards (f : Type -> Type) (a : Type) : Type where
  constructor backwards
  field forwards : f a

open Backwards public

instance
  Functor-Backwards : {{Functor f}} -> Functor (Backwards f)
  Functor-Backwards .map f (backwards x) = backwards (map f x)

  Applicative-Backwards : {{Applicative f}} -> Applicative (Backwards f)
  Applicative-Backwards .pure x = backwards (pure x)
  Applicative-Backwards ._<*>_ (backwards f) (backwards x) =
    backwards (| x & f |)
