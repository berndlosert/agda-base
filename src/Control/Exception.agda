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
    a b e : Set

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

  catchJust : (e -> Maybe b) -> IO a -> (b -> IO a) -> IO a
  catchJust p a handler = catch a \ e -> case p e of \ where
    Nothing -> throwIO e
    (Just b) -> handler b

  handle : (e -> IO a) -> IO a -> IO a
  handle = flip catch

  handleJust : (e -> Maybe b) -> (b -> IO a) -> IO a -> IO a
  handleJust = flip <<< catchJust

  try : IO a -> IO (Either e a)
  try a = catch (a >>= \ v -> return (Right v)) (\ e -> return (Left e))

  tryJust : (e -> Maybe b) -> IO a -> IO (Either b a)
  tryJust p a = do
    r <- try a
    case r of \ where
      (Right v) -> return (Right v)
      (Left e) -> case p e of \ where
        Nothing -> throwIO e
        (Just b) -> return (Left b)

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
