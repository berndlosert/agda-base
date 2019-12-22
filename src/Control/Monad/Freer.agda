{-# OPTIONS --type-in-type #-}

module Control.Monad.Freer where

-- The "Church" encoding of monads on Sets is called Freer. 

record Freer (F : Set -> Set) (X : Set) : Set where
  constructor Freer:
  field
    run : forall {Y} -> (X -> Y) -> (F Y -> Y) -> Y

open Freer

-- Freer F is a functor.

open import Control.Category
open import Data.Functor

instance
  Functor:Freer : forall {F} -> Endofunctor Sets (Freer F)
  Functor:Freer .map f free gen alg = runFreer free (gen <<< f) alg

-- Freer F is a monad. Note that it doesn't require F to be a functor.

open import Control.Monad

Monad:Freer : forall {F} -> Monad Sets (Freer F)
Monad:Freer {F} = Triple: ext ret 
  where
    ext : forall {X Z} -> (X -> Freer F Z) -> Freer F X -> Freer F Z
    ext f free gen alg = runFreer free (\ x -> f x gen alg) alg

    ret : forall {X} -> X -> Freer F X
    ret x gen alg = gen x
