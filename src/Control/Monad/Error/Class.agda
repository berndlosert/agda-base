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
    a b r : Set

-------------------------------------------------------------------------------
-- MonadThrow
-------------------------------------------------------------------------------

record MonadThrow (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    throw : e -> m a

open MonadThrow {{...}} public

-------------------------------------------------------------------------------
-- MonadError
-------------------------------------------------------------------------------

record MonadError (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{MonadThrow-super}} : MonadThrow e m
    catch : m a -> (e -> m a) -> m a

  catchJust : (e -> Maybe b) -> m a -> (b -> m a) -> m a
  catchJust p a handler = catch a (\ e -> maybe (throw e) handler (p e))

  handle : (e -> m a) -> m a -> m a
  handle = flip catch

  handleJust : (e -> Maybe b) -> (b -> m a) -> m a -> m a
  handleJust = flip <<< catchJust

  try : m a -> m (e + a)
  try a = catch (map Right a) (pure <<< Left)

  tryJust : (e -> Maybe b) -> m a -> m (b + a)
  tryJust p a = do
    r <- try a
    case r of \ where
      (Right v) -> return (Right v)
      (Left e) -> maybe (throw e) (return <<< Left) (p e)

  withResource : m r -> (r -> m Unit) -> (r -> m a) -> m a
  withResource acquire release kleisli = do
    resource <- acquire
    result <- try (kleisli resource)
    release resource
    either throw pure result

open MonadError {{...}} public
