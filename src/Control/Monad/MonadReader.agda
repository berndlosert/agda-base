{-# OPTIONS --type-in-type #-}

module Control.Monad.MonadReader where

open import Prelude

private
  variable
    A R : Set

record MonadReader (R : Set) (M : Set -> Set) : Set where
  field
    {{monad}} : Monad M
    ask : M R
    local : (R -> R) -> M ~> M

  asks : (R -> A) -> M A
  asks f = do
    r <- ask
    return (f r)

open MonadReader {{...}} public
  hiding (monad)
