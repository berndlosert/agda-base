module Data.Profunctor.Strong where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Profunctor

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
    strongl : p a b -> p (Pair a c) (Pair b c)

  strongr : p a b -> p (Pair c a) (Pair c b)
  strongr c = dimap swap swap (strongl c)

  infixr 3 _***_
  _***_ : {{Category p}} -> p a b -> p c d -> p (Pair a c) (Pair b d)
  f *** g = strongl f >>> strongr g

  infixr 3 _&&&_
  _&&&_ : {{Category p}} -> p a b -> p a c -> p a (Pair b c)
  f &&& g = arr dup >>> strongr g >>> strongl f

open Strong {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Strong-Function : Strong Function
  Strong-Function .strongl f (a , c) = (f a , c)
