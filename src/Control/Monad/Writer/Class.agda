{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- MonadWriter
-------------------------------------------------------------------------------

record MonadWriter (w : Type) (m : Type -> Type) : Type where
  field
    overlap {{Monoid-w}} : Monoid w
    overlap {{Monad-m}} : Monad m
    tell : w -> m Unit
    listen : m a -> m (a * w)
    pass : m (a * (w -> w)) -> m a

  writer : a * w -> m a
  writer (a , w) = do
    tell w
    pure a

  listens : (w -> b) -> m a -> m (a * b)
  listens f m = do
    (a , w) <- listen m
    pure (a , f w)

  censor : (w -> w) -> m a -> m a
  censor f m = pass do
    a <- m
    pure (a , f)

open MonadWriter {{...}} public
