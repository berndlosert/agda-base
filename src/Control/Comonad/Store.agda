{-# OPTIONS --type-in-type #-}

module Control.Comonad.Store where

open import Control.Comonad
open import Prelude

private variable s : Set

-- Store S is the dual of State S.
Store : Set -> Set -> Set
Store s a = (s -> a) * s

-- Store S is a functor.
instance
  functorStore : Functor (Store s)
  functorStore .map f (g , s) = (f ∘ g , s)

  comonadStore : Comonad (Store s)
  comonadStore .extend f (g , s) = ((λ _ -> f (g , s)) , s)
  comonadStore .extract (g , s) = g s
