{-# OPTIONS --type-in-type #-}

module Control.Monad.IO.Unlift where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.IO.Class

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- MonadUnliftIO
-------------------------------------------------------------------------------

record MonadUnliftIO (m : Type -> Type) : Type where
  field
    overlap {{MonadIO-super}} : MonadIO m
    withRunInIO : ((forall {a} -> m a -> IO a) -> IO b) -> m b

open MonadUnliftIO {{...}} public

instance
  MonadUnliftIO-IO : MonadUnliftIO IO
  MonadUnliftIO-IO .withRunInIO inner = inner id
