module Control.Monad.IO.Class where

open import Prelude

record MonadIO (m : Set -> Set) : Set where
  field
    overlap {{super}} : Monad m
    liftIO : IO ~> m

open MonadIO {{...}} public

instance
  MonadIO-IO : MonadIO IO
  MonadIO-IO .liftIO = id
