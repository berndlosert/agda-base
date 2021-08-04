{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader.Class where

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
-- MonadReader
-------------------------------------------------------------------------------
record MonadReader (r : Type) (m : Type -> Type) : Type where
  field
    overlap {{Monad-m}} : Monad m
    ask : m r
    local : (r -> r) -> m a -> m a

  asks : (r -> a) -> m a
  asks f = do
    r <- ask
    pure (f r)

open MonadReader {{...}} public
