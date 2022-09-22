module Data.Profunctor.Strong where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Category
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
    mapFst : p a b -> p (Pair a c) (Pair b c)

  mapSnd : p a b -> p (Pair c a) (Pair c b)
  mapSnd = dimap swap swap <<< mapFst

  infixr 3 _***_
  _***_ : {{Category p}} -> p a b -> p c d -> p (Pair a c) (Pair b d)
  f *** g = (mapFst f) andThen (mapSnd g)

  infixr 3 _&&&_
  _&&&_ : {{Category p}} -> p a b -> p a c -> p a (Pair b c)
  f &&& g = (arr dup) andThen (mapSnd g) andThen (mapFst f)

open Strong {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Strong-Function : Strong Function
  Strong-Function .mapFst f (a , c) = (f a , c)
