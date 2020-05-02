{-# OPTIONS --type-in-type #-}

module Control.Monad.State.Class where

open import Prelude

private variable A : Set

record MonadState (S : Set) (M : Set -> Set) : Set where
  field
    {{monad}} : Monad M
    get : M S
    put : S -> M Unit

  state : (S -> Tuple A S) -> M A
  state f = do
    s₀ <- get
    let (a , s₁) = f s₀
    put s₁
    return a

  modify : (S -> S) -> M Unit
  modify f = state (λ s -> (unit , f s))

  gets : (S -> A) -> M A
  gets f = do
    s <- get
    return (f s)

open MonadState {{...}} public
