{-# OPTIONS --type-in-type #-}

module System.Time where

open import Prelude

open import Data.Time.Units

private
  postulate
    primGetTime : IO Nat
    primGetCPUTime : IO Nat

postulate
  cpuTimePrecision : Nat

getTime : IO Second
getTime = map _sec primGetTime

getCPUTime : IO Picosecond
getCPUTime = map _psec primGetCPUTime

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

{-# COMPILE GHC primGetTime = primGetTime #-}
{-# COMPILE GHC primGetCPUTime = getCPUTime #-}
{-# COMPILE GHC cpuTimePrecision = cpuTimePrecision #-}
