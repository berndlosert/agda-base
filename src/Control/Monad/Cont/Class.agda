{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont.Class where

open import Prelude

private variable a b : Set

record MonadCont (m : Set -> Set) : Set where
  field
    overlap {{monad}} : Monad m
    callCC : ((a -> m b) -> m a) -> m a

open MonadCont {{...}} public
