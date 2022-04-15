module Control.Concurrent where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- ThreadId
-------------------------------------------------------------------------------

postulate
  ThreadId : Set

private
  postulate
    threadIdEq : ThreadId -> ThreadId -> Bool
    threadIdLess : ThreadId -> ThreadId -> Bool
    threadIdShow : ThreadId -> String

instance
  Eq-ThreadId : Eq ThreadId
  Eq-ThreadId ._==_ = threadIdEq

  Ord-ThreadId : Ord ThreadId
  Ord-ThreadId ._<_ = threadIdLess

  Show-ThreadId : Show ThreadId
  Show-ThreadId .showsPrec _ = showString <<< threadIdShow

postulate
  myThreadId : IO ThreadId
  threadDelay : (microseconds : Nat) -> IO Unit
  forkIO : IO Unit -> IO ThreadId
  forkFinally : IO a -> (Either SomeException a -> IO Unit) -> IO ThreadId
  killThread : ThreadId -> IO Unit
  yield : IO Unit
  timeout : (microseconds : Nat) -> IO a -> IO (Maybe a)

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import System.Timeout #-}
{-# FOREIGN GHC import Control.Concurrent #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# COMPILE GHC ThreadId = type ThreadId #-}
{-# COMPILE GHC threadIdEq = (==) #-}
{-# COMPILE GHC threadIdLess = (<) #-}
{-# COMPILE GHC threadIdShow = pack . show #-}
{-# COMPILE GHC threadDelay = threadDelay . fromInteger #-}
{-# COMPILE GHC myThreadId = myThreadId #-}
{-# COMPILE GHC forkIO = forkIO #-}
{-# COMPILE GHC forkFinally = \ _ -> forkFinally #-}
{-# COMPILE GHC killThread = killThread #-}
{-# COMPILE GHC yield = yield #-}
{-# COMPILE GHC timeout = \ _ -> timeout . fromInteger #-}