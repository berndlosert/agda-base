{-# OPTIONS --type-in-type #-}

module Control.Monad.MonadState where

open import Prelude

record MonadState (S : Set) (M : Set -> Set) : Set where
  field
    {{monadMonadState}} M
