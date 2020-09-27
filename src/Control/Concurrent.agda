{-# OPTIONS --type-in-type #-}

module Control.Concurrent where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Exception
open import Data.Time.Units

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
    primEqThreadId : ThreadId -> ThreadId -> Bool
    primLessThanThreadId : ThreadId -> ThreadId -> Bool
    primShowThreadId : ThreadId -> String
    primThreadDelay : Nat -> IO Unit

threadDelay : {{_ : TimeUnit a}} -> a -> IO Unit
threadDelay = primThreadDelay <<< toMicroseconds

instance
  Eq-ThreadId : Eq ThreadId
  Eq-ThreadId ._==_ = primEqThreadId

  Ord-ThreadId : Ord ThreadId
  Ord-ThreadId ._<_ = primLessThanThreadId

  Show-ThreadId : Show ThreadId
  Show-ThreadId .showsPrec _ = showString <<< primShowThreadId

postulate
  myThreadId : IO ThreadId
  forkIO : IO Unit -> IO ThreadId
  forkFinally : IO a -> (SomeException + a -> IO Unit) -> IO ThreadId
  killThread : ThreadId -> IO Unit
  yield : IO Unit

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Control.Concurrent #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# COMPILE GHC ThreadId = type ThreadId #-}
{-# COMPILE GHC primEqThreadId = \ t1 t2 -> t1 == t2 #-}
{-# COMPILE GHC primLessThanThreadId = \ t1 t2 -> t1 < t2 #-}
{-# COMPILE GHC primShowThreadId = \ t -> pack (show t) #-}
{-# COMPILE GHC primThreadDelay = \ t -> threadDelay (fromInteger t) #-}
{-# COMPILE GHC myThreadId = myThreadId #-}
{-# COMPILE GHC forkIO = forkIO #-}
{-# COMPILE GHC forkFinally = \ _ -> forkFinally #-}
{-# COMPILE GHC killThread = killThread #-}
{-# COMPILE GHC yield = yield #-}
