{-# OPTIONS --type-in-type #-}

module System.Time where

open import Prelude

postulate
  getTime : IO Nat
  getCPUTime : IO Nat
  cpuTimePrecision : Nat

{-# FOREIGN GHC
  import Foreign.C (CTime (..))
  import Foreign.Ptr (Ptr, nullPtr)
  import System.CPUTime (getCPUTime, cpuTimePrecision)

  foreign import ccall "time" readtime :: Ptr a -> IO CTime
  primGetTime :: IO Integer
  primGetTime = do
    CTime t <- readtime nullPtr
    return (toInteger t)
#-}

{-# COMPILE GHC getTime = primGetTime #-}
{-# COMPILE GHC getCPUTime = getCPUTime #-}
{-# COMPILE GHC cpuTimePrecision = cpuTimePrecision #-}
