module Properties.Functor where

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
      f : Type -> Type

-------------------------------------------------------------------------------
-- Functor Properties
-------------------------------------------------------------------------------

module _ {{_ : Functor f}} where

  preservesComposition : {{Eq (f c)}}
    -> (a -> b) -> (b -> c) -> f a -> Bool
  preservesComposition f g x = map (g <<< f) x == (map g <<< map f) x

  preservesIdentity : {{Eq (f a)}} -> f a -> Bool
  preservesIdentity x = map id x == x