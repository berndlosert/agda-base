{-# OPTIONS --type-in-type #-}

module Control.Monad.MonadTrans where

open import Prelude

private
  variable
    M : Set -> Set

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    lift : {{_ : Monad M}} -> M ~> T M
    transform : {{_ : Monad M}} -> Monad (T M)

open MonadTrans {{...}} public
