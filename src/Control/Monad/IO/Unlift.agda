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
    a b : Set

-------------------------------------------------------------------------------
-- MonadUnliftIO
-------------------------------------------------------------------------------

record MonadUnliftIO (m : Set -> Set) : Set where
  field
    overlap {{MonadIO-super}} : MonadIO m
    withRunInIO : ((forall {a} -> m a -> IO a) -> IO b) -> m b

open MonadUnliftIO {{...}} public

instance
  MonadUnliftIO-IO : MonadUnliftIO IO
  MonadUnliftIO-IO .withRunInIO inner = inner id
