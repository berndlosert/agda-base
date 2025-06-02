module System.IO.Error where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type

-------------------------------------------------------------------------------
-- IOError
-------------------------------------------------------------------------------

postulate
  IOError : Type
  ioError : IOError -> IO a
  catchIOError : IO a -> (IOError -> IO a) -> IO a
  bracketIO : IO a -> (a -> IO b) -> (a -> IO c) -> IO c
  userError : String -> IOError

{-# FOREIGN GHC import System.IO.Error #-}
{-# FOREIGN GHC import Control.Exception (bracket) #-}
{-# FOREIGN GHC import Data.Text (unpack) #-}
{-# COMPILE GHC IOError = type IOError #-}
{-# COMPILE GHC ioError = \ _ -> ioError #-}
{-# COMPILE GHC catchIOError = \ _ -> catchIOError #-}
{-# COMPILE GHC bracketIO = \ _ _ _ -> bracket #-}
{-# COMPILE GHC userError = userError . unpack #-}
