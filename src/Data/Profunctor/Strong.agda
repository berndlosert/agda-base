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
    a b c d : Set

-------------------------------------------------------------------------------
-- Strong
-------------------------------------------------------------------------------

record Strong (p : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor-super}} : Profunctor p
    first : p a b -> p (Pair a c) (Pair b c)

  second : p a b -> p (Pair c a) (Pair c b)
  second c = dimap swap swap (first c)

  infixr 3 _***_
  _***_ : {{Category p}} -> p a b -> p c d -> p (Pair a c) (Pair b d)
  f *** g = first f >>> second g

  infixr 3 _&&&_
  _&&&_ : {{Category p}} -> p a b -> p a c -> p a (Pair b c)
  f &&& g = arr dup >>> second g >>> first f

open Strong {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Strong-Function : Strong Function
  Strong-Function .first f (a , c) = (f a , c)
