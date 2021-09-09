{-# OPTIONS --type-in-type #-}

module Control.Monad.State.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- MonadState
-------------------------------------------------------------------------------

record MonadState (s : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    state : (s -> Pair s a) -> m a

  get : m s
  get = state \ s -> (s , s)

  put : s -> m Unit
  put s = state \ _ -> (s , tt)

  modify : (s -> s) -> m Unit
  modify f = state \ s -> (f s , tt)

  gets : (s -> a) -> m a
  gets f = do
    s <- get
    pure (f s)

open MonadState {{...}} public
