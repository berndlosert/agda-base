{-# OPTIONS --type-in-type #-}

module Control.Monad.Error.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a e : Set

-------------------------------------------------------------------------------
-- MonadError
-------------------------------------------------------------------------------

record MonadError (e : Set) (m : Set -> Set) : Set where
  field
    overlap {{Monad-super}} : Monad m
    raiseError : e -> m a
    handleError : m a -> (e -> m a) -> m a

open MonadError {{...}} public

instance
  MonadError-Maybe : MonadError Unit Maybe
  MonadError-Maybe .raiseError _ = nothing
  MonadError-Maybe .handleError nothing h = h tt
  MonadError-Maybe .handleError x _ = x

  MonadError-Either : MonadError e (Either e)
  MonadError-Either .raiseError = left
  MonadError-Either .handleError (left e) h = h e
  MonadError-Either .handleError x _ = x

  MonadError-IO : MonadError IOException IO
  MonadError-IO .raiseError = throw
  MonadError-IO .handleError = catch
