{-# OPTIONS --type-in-type #-}

module Control.Monad.Base where

open import Prelude

record MonadBase (M N : Set -> Set) : Set where
  field liftBase : M ~> N

open MonadBase {{...}} public
