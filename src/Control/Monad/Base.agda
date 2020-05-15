{-# OPTIONS --type-in-type #-}

module Control.Monad.Base where

open import Prelude

record MonadBase (B M : Set -> Set) : Set where
  field liftBase : B ~> M

open MonadBase {{...}} public
