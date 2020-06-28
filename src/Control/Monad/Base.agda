{-# OPTIONS --type-in-type #-}

module Control.Monad.Base where

open import Prelude

record MonadBase (m n : Set -> Set) : Set where
  field liftBase : m ~> n

open MonadBase {{...}} public
