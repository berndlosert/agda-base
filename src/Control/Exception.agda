{-# OPTIONS --type-in-type #-}

module Control.Exception where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Error.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Error.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c e : Set

-------------------------------------------------------------------------------
-- Exception, SomeException, and related functions
-------------------------------------------------------------------------------

postulate
  Exception : Set -> Set

  SomeException : Set
  IOException : Set

  bracket : IO a -> (a -> IO b) -> (a -> IO c) -> IO c
  bracketOnError : IO a -> (a -> IO b) -> (a -> IO c) -> IO c
  finally : IO a -> IO b -> IO a
  onException : IO a -> IO b -> IO a

  instance
    Exception-SomeException : Exception SomeException
    Exception-IOException : Exception IOException

module _ {{_ : Exception e}} where

  postulate
    toException : e -> SomeException
    fromException : SomeException -> Maybe e
    displayException : e -> String

    unsafeThrow : e -> a
    throwIO : e -> IO a
    catchIO : IO a -> (e -> IO a) -> IO a

  instance
    MonadThrow-IO : MonadThrow e IO
    MonadThrow-IO .throw = throwIO

    MonadError-IO : MonadError e IO
    MonadError-IO .catch = catchIO

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# FOREIGN GHC data ExceptionDict e = Exception e => ExceptionDict #-}
{-# COMPILE GHC Exception = type ExceptionDict #-}
{-# COMPILE GHC SomeException = type SomeException #-}
{-# COMPILE GHC IOException = type IOException #-}
{-# COMPILE GHC Exception-SomeException = ExceptionDict #-}
{-# COMPILE GHC Exception-IOException = ExceptionDict #-}
{-# COMPILE GHC toException = \ _ ExceptionDict -> toException #-}
{-# COMPILE GHC fromException = \ _ ExceptionDict -> fromException #-}
{-# COMPILE GHC displayException = \ _ ExceptionDict -> pack . displayException #-}
{-# COMPILE GHC unsafeThrow = \ _ ExceptionDict _ -> throw #-}
{-# COMPILE GHC throwIO = \ _ ExceptionDict _ -> throwIO #-}
{-# COMPILE GHC catchIO = \ _ ExceptionDict _ -> catch #-}
{-# COMPILE GHC bracket = \ _ _ _ -> bracket #-}
{-# COMPILE GHC bracketOnError = \ _ _ _ -> bracketOnError #-}
{-# COMPILE GHC finally = \ _ _ -> finally #-}
{-# COMPILE GHC finally = \ _ _ -> onException #-}
