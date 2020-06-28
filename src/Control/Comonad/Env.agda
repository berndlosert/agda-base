{-# OPTIONS --type-in-type #-}

module Control.Comonad.Env where

open import Control.Comonad
open import Prelude

private variable e : Set

-- The enivornment comonad. This is the dual of the Reader monad.
Env : Set -> Set -> Set
Env e a = e * a

instance
  functorEnv : Functor (Env e)
  functorEnv .map f (e , x) = (e , f x)

  comonadEnv : Comonad (Env e)
  comonadEnv .extend f p@(e , x) = (e , f p)
  comonadEnv .extract (e , x) = x
