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
    a : Type

-------------------------------------------------------------------------------
-- MonadIO
-------------------------------------------------------------------------------

record MonadIO (m : Type -> Type) : Type where
  field
    overlap {{Monad-super}} : Monad m
    liftIO : IO a -> m a

open MonadIO {{...}} public

instance
  MonadIO-IO : MonadIO IO
  MonadIO-IO .liftIO = id
