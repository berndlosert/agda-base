{-# OPTIONS --type-in-type #-}

module Data.Profunctor.Strong where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c d : Type

-------------------------------------------------------------------------------
-- Strong
-------------------------------------------------------------------------------

record Strong (p : Type -> Type -> Type) : Type where
  field
    overlap {{Profunctor-super}} : Profunctor p
    first : p a b -> p (a * c) (b * c)

  second : p a b -> p (c * a) (c * b)
  second c = dimap swap swap (first c)

  infixr 3 _***_
  _***_ : {{_ : Category p}} -> p a b -> p c d -> p (a * c) (b * d)
  f *** g = first f >>> second g

  infixr 3 _&&&_
  _&&&_ : {{_ : Category p}} -> p a b -> p a c -> p a (b * c)
  f &&& g = arr dup >>> second g >>> first f

open Strong {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Strong-Function : Strong Function
  Strong-Function .first f (a , c) = (f a , c)
