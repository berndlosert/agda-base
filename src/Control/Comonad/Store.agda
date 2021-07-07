{-# OPTIONS --type-in-type #-}

module Control.Comonad.Store where

open import Control.Comonad
open import Prelude

private variable s : Type

-- Store S is the dual of State S.
Store : Type -> Type -> Type
Store s a = (s -> a) * s

-- Store S is a functor.
instance
  Functor-Store : Functor (Store s)
  Functor-Store .map f (g , s) = (f <<< g , s)

  Comonad-Store : Comonad (Store s)
  Comonad-Store .extend f (g , s) = ((\ _ -> f (g , s)) , s)
  Comonad-Store .extract (g , s) = g s
