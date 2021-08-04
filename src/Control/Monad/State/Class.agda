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
    a : Type

-------------------------------------------------------------------------------
-- MonadState
-------------------------------------------------------------------------------

record MonadState (s : Type) (m : Type -> Type) : Type where
  field
    overlap {{Monad-super}} : Monad m
    state : (s -> a * s) -> m a

  get : m s
  get = state \ s -> (s , s)

  put : s -> m Unit
  put s = state \ _ -> (unit , s)

  modify : (s -> s) -> m Unit
  modify f = state \ s -> (unit , f s)

  gets : (s -> a) -> m a
  gets f = do
    s <- get
    pure (f s)

open MonadState {{...}} public
