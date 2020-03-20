{-# OPTIONS --type-in-type #-}

module Control.Comonad.Env where

open import Control.Comonad
open import Prelude

private
  variable
    E : Set

-- The enivornment comonad. This is the dual of the Reader monad.
Env : Set -> Set -> Set
Env E Y = E * Y

instance
  functorEnv : Functor (Env E)
  functorEnv .map f (e , x) = (e , f x)

  comonadEnv : Comonad (Env E)
  comonadEnv .extend f p@(e , x) = (e , f p)
  comonadEnv .extract (e , x) = x
