module System.IO.Unsafe where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import System.IO using (IO)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private variable a : Type

-------------------------------------------------------------------------------
-- Unsafe functions
-------------------------------------------------------------------------------

postulate
  unsafePerformIO : IO a -> a

{-# FOREIGN GHC import qualified System.IO.Unsafe as U #-}
{-# COMPILE GHC unsafePerformIO = \ _ io -> U.unsafePerformIO io #-}
