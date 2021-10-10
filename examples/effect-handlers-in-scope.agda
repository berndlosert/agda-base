{-# OPTIONS --type-in-type #-}

open import Prelude

open import Control.Monad.State
open import Control.Exception

variable
  m : Set -> Set

decr : {{MonadState Nat m}} -> {{MonadThrow Unit m}} -> m Unit
decr = do
  n <- get
  case n of \ where
    0 -> throw tt
    (suc m) -> put m
