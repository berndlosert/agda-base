{-# OPTIONS --type-in-type #-}

module Control.Concurrent where

open import Prelude

postulate
  ThreadId : Set

  myThreadId : IO ThreadId
  fork : IO Unit -> IO ThreadId
  kill : ThreadId -> IO Unit
  yield : IO Unit
  microDelay : Nat -> IO Unit

private
  postulate
    primEqThreadId : ThreadId -> ThreadId -> Bool
    primLessThanThreadId : ThreadId -> ThreadId -> Bool
    primShowThreadId : ThreadId -> String

instance
  eqThreadId : Eq ThreadId
  eqThreadId ._==_ = primEqThreadId

  ordThreadId : Ord ThreadId
  ordThreadId ._<_ = primLessThanThreadId

  showThreadId : Show ThreadId
  showThreadId .show = primShowThreadId

delay : Nat -> IO Unit
delay n = microDelay $ n * 10 ^ 6

{-# FOREIGN GHC import Control.Concurrent #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# COMPILE GHC ThreadId = type ThreadId #-}
{-# COMPILE GHC primEqThreadId = \ t1 t2 -> t1 == t2 #-}
{-# COMPILE GHC primLessThanThreadId = \ t1 t2 -> t1 < t2 #-}
{-# COMPILE GHC primShowThreadId = \ t -> pack (show t) #-}
{-# COMPILE GHC fork = forkIO #-}
{-# COMPILE GHC kill = killThread #-}
{-# COMPILE GHC yield = yield #-}
{-# COMPILE GHC microDelay = \ t -> threadDelay (fromInteger t) #-}
