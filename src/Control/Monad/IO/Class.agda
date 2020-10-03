{-# OPTIONS --type-in-type #-}

module Control.Monad.IO.Class where

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
-- MonadIO
-------------------------------------------------------------------------------

record MonadIO (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    liftIO : IO a -> m a

open MonadIO {{...}} public

instance
  MonadIO-IO : MonadIO IO
  MonadIO-IO .liftIO = id
