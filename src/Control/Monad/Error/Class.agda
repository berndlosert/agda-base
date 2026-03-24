module Control.Monad.Error.Class where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad using (Monad)
open import Control.Monad.Instances using (Monad-Maybe)
open import System.IO using (IO)
open import System.IO.Error using (IOError; ioError)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c e : Type

-------------------------------------------------------------------------------
-- MonadError
-------------------------------------------------------------------------------

record MonadError (e : Type) (m : Type -> Type) : Type where
  field
    overlap {{Monad-super}} : Monad m
    throwError : e -> m a

open MonadError {{...}} public

instance
  MonadError-Maybe : MonadError Unit Maybe
  MonadError-Maybe .throwError _ = nothing

  MonadError-Either : MonadError e (Either e)
  MonadError-Either .throwError = left

  MonadError-IO : MonadError IOError IO
  MonadError-IO .throwError = ioError
