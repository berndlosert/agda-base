{-# OPTIONS --type-in-type #-}

module Control.Monad.IO.Class where

open import Prelude

private variable a : Set

record MonadIO (m : Set -> Set) : Set where
  field
    overlap {{super}} : Monad m
    liftIO : IO a -> m a

open MonadIO {{...}} public

instance
  MonadIO-IO : MonadIO IO
  MonadIO-IO .liftIO = id
