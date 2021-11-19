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
  infixl 9 _catchError_
  field
    overlap {{Monad-super}} : Monad m
    throwError : e -> m a
    _catchError_ : m a -> (e -> m a) -> m a

open MonadError {{...}} public

instance
  MonadError-Maybe : MonadError Unit Maybe
  MonadError-Maybe .throwError _ = nothing
  MonadError-Maybe ._catchError_ nothing h = h tt
  MonadError-Maybe ._catchError_ x _ = x

  MonadError-Either : MonadError e (Either e)
  MonadError-Either .throwError = left
  MonadError-Either ._catchError_ (left e) h = h e
  MonadError-Either ._catchError_ x _ = x

  MonadError-IO : MonadError IOException IO
  MonadError-IO .throwError = throw
  MonadError-IO ._catchError_ = _catch_
