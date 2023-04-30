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
    a b c d : Type

-------------------------------------------------------------------------------
-- Strong
-------------------------------------------------------------------------------

record Strong (p : Type -> Type -> Type) : Type where
  field
    overlap {{Profunctor-super}} : Profunctor p
    mapFst : p a b -> p (Tuple a c) (Tuple b c)

  mapSnd : p a b -> p (Tuple c a) (Tuple c b)
  mapSnd = dimap swap swap <<< mapFst

  infixr 3 _***_
  _***_ : {{Category p}} -> p a b -> p c d -> p (Tuple a c) (Tuple b d)
  f *** g = mapFst f >>> mapSnd g

  infixr 3 _&&&_
  _&&&_ : {{Category p}} -> p a b -> p a c -> p a (Tuple b c)
  f &&& g = arr dup >>> (f *** g)

  uncurry : p a (b -> c) -> p (Tuple a b) c
  uncurry = mapFst >>> map \ { (f , x) -> f x }

open Strong {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Strong-Function : Strong Function
  Strong-Function .mapFst f (a , c) = (f a , c)
