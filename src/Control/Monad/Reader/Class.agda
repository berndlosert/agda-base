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
    a : Set

-------------------------------------------------------------------------------
-- MonadReader
-------------------------------------------------------------------------------
record MonadReader (r : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    ask : m r
    local : (r -> r) -> m a -> m a

  asks : (r -> a) -> m a
  asks f = do
    r <- ask
    return (f r)

open MonadReader {{...}} public
