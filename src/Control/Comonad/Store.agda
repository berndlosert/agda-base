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
  functorStore .map f (g , s) = (g >>> f , s)

  comonadStore : Comonad (Store S)
  comonadStore .extend f (g , s) = (_,_ g >>> f , s)
  comonadStore .extract (g , s) = g s
