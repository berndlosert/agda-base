module Control.Concurrent where

open import Prelude

open import Data.Time.Units
open import System.IO

private variable a : Set

postulate
  ThreadId : Set
  myThreadId : IO ThreadId
  forkIO : IO Unit -> IO ThreadId
  killThread : ThreadId -> IO Unit
  yield : IO Unit

private
  postulate
    primEqThreadId : ThreadId -> ThreadId -> Bool
    primLessThanThreadId : ThreadId -> ThreadId -> Bool
    primShowThreadId : ThreadId -> String
    primThreadDelay : Nat -> IO Unit

instance
  EqThreadId : Eq ThreadId
  EqThreadId ._==_ = primEqThreadId

  OrdThreadId : Ord ThreadId
  OrdThreadId ._<_ = primLessThanThreadId

  ShowThreadId : Show ThreadId
  ShowThreadId .showsPrec _ = showString ∘ primShowThreadId

threadDelay : {{_ : TimeUnit a}} -> a -> IO Unit
threadDelay x = primThreadDelay (toMicroseconds x)

{-# FOREIGN GHC import Control.Concurrent #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# COMPILE GHC ThreadId = type ThreadId #-}
{-# COMPILE GHC primEqThreadId = \ t1 t2 -> t1 == t2 #-}
{-# COMPILE GHC primLessThanThreadId = \ t1 t2 -> t1 < t2 #-}
{-# COMPILE GHC primShowThreadId = \ t -> pack (show t) #-}
{-# COMPILE GHC forkIO = forkIO #-}
{-# COMPILE GHC killThread = killThread #-}
{-# COMPILE GHC yield = yield #-}
{-# COMPILE GHC primThreadDelay = \ t -> threadDelay (fromInteger t) #-}
