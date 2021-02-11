{-# OPTIONS --type-in-type #-}

module System.Time where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

postulate
  getPOSIXTime : IO Nat -- in seconds
  getCPUTime : IO Nat -- in picoseconds
  cpuTimePrecision : Nat

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC
  import Foreign.C (CTime (..))
  import Foreign.Ptr (Ptr, nullPtr)
  import System.CPUTime (getCPUTime, cpuTimePrecision)

  foreign import ccall "time" readtime :: Ptr a -> IO CTime
  getPOSIXTime :: IO Integer
  getPOSIXTime = do
    CTime t <- readtime nullPtr
    return (toInteger t)
#-}

{-# COMPILE GHC getPOSIXTime = getPOSIXTime #-}
{-# COMPILE GHC getCPUTime = getCPUTime #-}
{-# COMPILE GHC cpuTimePrecision = cpuTimePrecision #-}
