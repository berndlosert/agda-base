{-# OPTIONS --type-in-type #-}

module Control.Monad.Free.Class where

open import Prelude

record MonadFree (F M : Set -> Set) : Set where
  field wrap : F ∘ M ~> M

open MonadFree {{...}} public
