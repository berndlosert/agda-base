{-# OPTIONS --type-in-type #-}

module Control.Comonad.Store where

open import Control.Comonad
open import Prelude

private
  variable
    S : Set

-- Store S is the dual of State S.
Store : Set -> Set -> Set
Store S X = (S -> X) * S

-- Store S is a functor.
instance
  Functor:Store : Functor (Store S)
  Functor:Store .map f (Pair: g s) = Pair: (g >>> f) s

  Comonad:Store : Comonad (Store S)
  Comonad:Store .extend f (Pair: g s) = Pair: (Pair: g >>> f) s
  Comonad:Store .extract (Pair: g s) = g s
