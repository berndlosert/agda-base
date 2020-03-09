{-# OPTIONS --type-in-type #-}

module Control.Comonad.Env where

open import Prelude

-- The enivornment comonad. This is the dual of the Reader monad.
Env : Set -> Set -> Set
Env E Y = E * Y

instance
  Functor:Env : forall {E} -> Functor Sets Sets (Env E)
  Functor:Env .map f (Pair: e x) = Pair: e (f x)

open import Control.Comonad

instance
  Comonad:Env : forall {E} -> Comonad Sets (Env E)
  Comonad:Env .coextend f p@(Pair: e x) = Pair: e (f p)
  Comonad:Env .extract (Pair: e x) = x
