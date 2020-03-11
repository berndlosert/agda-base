{-# OPTIONS --type-in-type #-}

module Control.Comonad.Store where

open import Prelude

-- Store S is the dual of State S.
Store : Set -> Set -> Set
Store S X = (S -> X) * S

-- Store S is a functor.
instance
  Functor:Store : forall {S} -> Functor (Store S)
  Functor:Store .map f (Pair: g s) = Pair: (g >>> f) s

-- Store S is a comonad.
open import Control.Comonad

instance
  Comonad:Store : forall {S} -> Comonad Sets (Store S)
  Comonad:Store .coextend f (Pair: g s) = Pair: (Pair: g >>> f) s
  Comonad:Store .extract (Pair: g s) = g s
