module Control.Monad.State.Class where

open import Prelude

private variable a : Set

record MonadState (s : Set) (m : Set -> Set) : Set where
  field
    overlap {{monad}} : Monad m
    get : m s
    put : s -> m Unit

  state : (s -> a * s) -> m a
  state f = do
    s0 <- get
    let (a , s1) = f s0
    put s1
    return a

  modify : (s -> s) -> m Unit
  modify f = state (\ s -> (unit , f s))

  gets : (s -> a) -> m a
  gets f = do
    s <- get
    return (f s)

open MonadState {{...}} public
