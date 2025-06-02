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
    state : (s -> Tuple s a) -> m a

  get : m s
  get = state \ s -> (s , s)

  put : s -> m Unit
  put s = state \ _ -> (s , tt)

  modify : (s -> s) -> m Unit
  modify f = state \ s -> (f s , tt)

  gets : (s -> a) -> m a
  gets f = (| f get |)

open MonadState {{...}} public
