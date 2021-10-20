module Control.Comonad.Store where

open import Control.Comonad
open import Prelude

private variable s : Set

-- Store S is the dual of State S.
Store : Set -> Set -> Set
Store s a = Pair (s -> a) s

-- Store S is a functor.
instance
  Functor-Store : Functor (Store s)
  Functor-Store .map f (g , s) = (f <<< g , s)

  Comonad-Store : Comonad (Store s)
  Comonad-Store .extend f (g , s) = ((\ _ -> f (g , s)) , s)
  Comonad-Store .extract (g , s) = g s
