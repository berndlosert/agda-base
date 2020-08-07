module Control.Comonad.Store where

open import Control.Comonad
open import Prelude

private variable s : Set

-- Store S is the dual of State S.
Store : Set -> Set -> Set
Store s a = (s -> a) * s

-- Store S is a functor.
instance
  FunctorStore : Functor (Store s)
  FunctorStore .map f (g , s) = (f ∘ g , s)

  ComonadStore : Comonad (Store s)
  ComonadStore .extend f (g , s) = ((λ _ -> f (g , s)) , s)
  ComonadStore .extract (g , s) = g s
