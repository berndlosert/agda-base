{-# OPTIONS --type-in-type #-}

module Control.Comonad.Env where

-- The enivornment comonad. This is the dual of the Reader monad.

open import Data.Pair
Env : Set -> Set -> Set
Env E Y = E * Y

open import Control.Category
open import Data.Functor

instance
  Functor:Env : forall {E} -> Endofunctor Sets (Env E)
  Functor:Env .map f (e , x) = (e , f x)

open import Control.Comonad

instance
  Comonad:Env : forall {E} -> Comonad Sets (Env E)
  Comonad:Env .duplicate (e , x) = (e , (e , x))
  Comonad:Env .extract (e , x) = x
