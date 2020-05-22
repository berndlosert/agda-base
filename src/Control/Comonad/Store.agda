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
  functorStore : Functor (Store S)
  functorStore .map f (g , s) = (f ∘ g , s)

  comonadStore : ∀ {S} -> Comonad (Store S)
  comonadStore {S} .extend f (g , s) = ((\ _ -> f (g , s)) , s)
  comonadStore .extract (g , s) = g s
