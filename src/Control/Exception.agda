{-# OPTIONS --type-in-type #-}

module Control.Exception where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Except.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Except.Class public

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

    MonadExcept-IO : MonadExcept e IO
    MonadExcept-IO .catch = catchIO

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC
  import Control.Exception
  import Data.Text (pack)

  data ExceptionDict e = Exception e => ExceptionDict

  saferBracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
  saferBracket before after thing = mask $ \ restore -> do
    x <- run before
    res1 <- try $ restore $ run $ thing x
    case res1 of
      Left (e1 :: SomeException) -> do
        _ :: Either SomeException b <-
            try $ uninterruptibleMask_ $ run $ after x
        throwIO e1
      Right y -> do
        _ <- uninterruptibleMask_ $ run $ after x
        return y

  saferBracketOnError :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
  saferBracketOnError before after thing = mask $ \ restore -> do
    x <- run before
    res1 <- try $ restore $ run $ thing x
    case res1 of
      Left (e1 :: SomeException) -> do
        _ :: Either SomeException b <-
          try $ uninterruptibleMask_ $ run $ after x
        throwIO e1
      Right y -> return y
#-}

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
{-# COMPILE GHC bracket = \ _ _ _ -> saferBracket #-}
{-# COMPILE GHC bracketOnError = \ _ _ _ -> saferBracketOnError #-}
{-# COMPILE GHC finally = \ _ _ -> finally #-}
{-# COMPILE GHC onException = \ _ _ -> onException #-}
