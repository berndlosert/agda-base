module Control.Comonad.Cofree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables 
-------------------------------------------------------------------------------

private
  variable
    a : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Cofree
-------------------------------------------------------------------------------

record Cofree (f : Set -> Set) (a : Set) : Set where
  coinductive
  field
    value : a
    unwrap : f (Cofree f a)  

instance 
  Functor-Cofree : {{Functor f}} -> Functor (Cofree f)
  Functor-Cofree .map f x = \ where 
    .Cofree.value -> f (Cofree.value x)
    .Cofree.unwrap -> map (map f) (Cofree.unwrap x) 

