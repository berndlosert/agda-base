{-# OPTIONS --type-in-type #-}

module Control.Exception where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
  instance Exception-SomeException : Exception SomeException

module _ {{_ : Exception e}} where

  postulate
    toException : e -> SomeException
    fromException : SomeException -> Maybe e
    displayException : e -> String

    throw : e -> a
    throwIO : e -> IO a

    catch : IO a -> (e -> IO a) -> IO a

    bracket : IO a -> (a -> IO b) -> (a -> IO c) -> IO c
    finally : IO a -> IO b -> IO a

  catchJust : (e -> Maybe b) -> IO a -> (b -> IO a) -> IO a
  catchJust p a handler = catch a (\ e -> maybe (throwIO e) handler (p e))

  handle : (e -> IO a) -> IO a -> IO a
  handle = flip catch

  handleJust : (e -> Maybe b) -> (b -> IO a) -> IO a -> IO a
  handleJust = flip <<< catchJust

  try : IO a -> IO (Either e a)
  try a = catch (a >>= Right >>> return) (Left >>> return)

  tryJust : (e -> Maybe b) -> IO a -> IO (Either b a)
  tryJust p a = do
    r <- try a
    case r of \ where
      (Right v) -> return (Right v)
      (Left e) -> maybe (throwIO e) (return <<< Left) (p e)

  onException : IO a -> IO b -> IO a
  onException io what = catch io \ e -> do
    _ <- what
    throwIO e

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# FOREIGN GHC data ExceptionDict e = Exception e => ExceptionDict #-}
{-# COMPILE GHC Exception = type ExceptionDict #-}
{-# COMPILE GHC SomeException = type SomeException #-}
{-# COMPILE GHC Exception-SomeException = ExceptionDict #-}
{-# COMPILE GHC toException = \ _ ExceptionDict -> toException #-}
{-# COMPILE GHC fromException = \ _ ExceptionDict -> fromException #-}
{-# COMPILE GHC displayException = \ _ ExceptionDict -> pack . displayException #-}
{-# COMPILE GHC throw = \ _ ExceptionDict _ -> throw #-}
{-# COMPILE GHC throwIO = \ _ ExceptionDict _ -> throwIO #-}
{-# COMPILE GHC catch = \ _ ExceptionDict _ -> catch #-}
{-# COMPILE GHC bracket = \ _ ExceptionDict _ _ _ -> bracket #-}
{-# COMPILE GHC finally = \ _ ExceptionDict _ _ -> finally #-}
