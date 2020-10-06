{-# OPTIONS --type-in-type #-}

module Control.Monad.Error.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a r : Set

-------------------------------------------------------------------------------
-- MonadThrow
-------------------------------------------------------------------------------

record MonadThrow (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    throwError : e -> m a

open MonadThrow {{...}} public

-------------------------------------------------------------------------------
-- MonadError
-------------------------------------------------------------------------------

record MonadError (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{MonadThrow-super}} : MonadThrow e m
    catchError : m a -> (e -> m a) -> m a

  try : m a -> m (e + a)
  try a = catchError (map Right a) (pure <<< Left)

  withResource : m r -> (r -> m Unit) -> (r -> m a) -> m a
  withResource acquire release kleisli = do
    resource <- acquire
    result <- try (kleisli resource)
    release resource
    either throwError pure result

open MonadError {{...}} public
