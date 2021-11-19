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
    throwError : e -> m a
    catchError : m a -> (e -> m a) -> m a

open MonadError {{...}} public

instance
  MonadError-Maybe : MonadError Unit Maybe
  MonadError-Maybe .throwError _ = nothing
  MonadError-Maybe .catchError nothing h = h tt
  MonadError-Maybe .catchError x _ = x

  MonadError-Either : MonadError e (Either e)
  MonadError-Either .throwError = left
  MonadError-Either .catchError (left e) h = h e
  MonadError-Either .catchError x _ = x

  MonadError-IO : MonadError IOException IO
  MonadError-IO .throwError = throw
  MonadError-IO .catchError = _catch_
