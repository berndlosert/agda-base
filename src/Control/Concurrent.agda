{-# OPTIONS --type-in-type #-}

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
    a : Type

-------------------------------------------------------------------------------
-- ThreadId
-------------------------------------------------------------------------------

postulate
  ThreadId : Type

private
  postulate
    threadIdEq : ThreadId -> ThreadId -> Bool
    threadIdCompare : ThreadId -> ThreadId -> Ordering
    threadIdShow : ThreadId -> String

instance
  Eq-ThreadId : Eq ThreadId
  Eq-ThreadId ._==_ = threadIdEq

  Ord-ThreadId : Ord ThreadId
  Ord-ThreadId .compare = threadIdCompare

  Show-ThreadId : Show ThreadId
  Show-ThreadId .showsPrec _ = showString <<< threadIdShow

postulate
  myThreadId : IO ThreadId
  threadDelay : (microseconds : Nat) -> IO Unit
  forkIO : IO Unit -> IO ThreadId
  forkFinally : IO a -> (Either SomeException a -> IO Unit) -> IO ThreadId
  killThread : ThreadId -> IO Unit
  yield : IO Unit

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Control.Concurrent #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# COMPILE GHC ThreadId = type ThreadId #-}
{-# COMPILE GHC threadIdEq = (==) #-}
{-# COMPILE GHC threadIdCompare = compare #-}
{-# COMPILE GHC threadIdShow = pack . show #-}
{-# COMPILE GHC threadDelay = threadDelay . fromInteger #-}
{-# COMPILE GHC myThreadId = myThreadId #-}
{-# COMPILE GHC forkIO = forkIO #-}
{-# COMPILE GHC forkFinally = \ _ -> forkFinally #-}
{-# COMPILE GHC killThread = killThread #-}
{-# COMPILE GHC yield = yield #-}
