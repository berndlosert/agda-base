{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Class where

open import Prelude

private variable a : Set

record MonadFree (f m : Set -> Set) : Set where
  field wrap : f (m a) -> m a

open MonadFree {{...}} public
