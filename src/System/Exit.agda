module System.Exit where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Int64

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- ExitCode
-------------------------------------------------------------------------------

data ExitCode : Set where
  ExitSuccess : ExitCode
  ExitFailure : Int64 -> ExitCode

{-# COMPILE GHC ExitCode = data ExitCode (ExitSuccess | ExitFailure) #-}

-------------------------------------------------------------------------------
-- Functions for exiting the program
-------------------------------------------------------------------------------

postulate
  exitWith : ExitCode -> IO a
  exitFailure : IO a
  exitSuccess : IO a
  die : String -> IO a

{-# FOREIGN GHC import System.Exit #-}
{-# FOREIGN GHC import Data.Text (unpack) #-}
{-# COMPILE GHC exitWith = \ _ -> exitWith #-}
{-# COMPILE GHC exitFailure = \ _ -> exitFailure #-}
{-# COMPILE GHC exitSuccess = \ _ -> exitSuccess #-}
{-# COMPILE GHC die = \ _ -> die . unpack #-}
