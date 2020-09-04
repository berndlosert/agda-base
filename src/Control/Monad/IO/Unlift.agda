module Control.Monad.IO.Unlift where

open import Prelude

open import Control.Monad.IO.Class

private variable b : Set

record MonadUnliftIO (m : Set -> Set) : Set where
  field
    overlap {{super}} : MonadIO m
    withRunInIO : ((m ~> IO) -> IO b) -> m b

open MonadUnliftIO {{...}} public

instance
  MonadUnliftIO-IO : MonadUnliftIO IO
  MonadUnliftIO-IO .withRunInIO inner = inner id
