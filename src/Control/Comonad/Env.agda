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
  Functor:Env : Functor (Env E)
  Functor:Env .map f (e , x) = (e , f x)

  Comonad:Env : Comonad (Env E)
  Comonad:Env .extend f p@(e , x) = (e , f p)
  Comonad:Env .extract (e , x) = x
