{-# OPTIONS --type-in-type #-}

module Control.Concurrent where

open import Prelude

open import Control.Monad.IO.Class
open import Control.Monad.IO.Unlift
open import Data.Time.Units

private
  variable
    a : Set
    m : Set -> Set

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

instance
  Eq-ThreadId : Eq ThreadId
  Eq-ThreadId ._==_ = primEqThreadId

  Ord-ThreadId : Ord ThreadId
  Ord-ThreadId ._<_ = primLessThanThreadId

  Show-ThreadId : Show ThreadId
  Show-ThreadId .showsPrec _ = showString <<< primShowThreadId

{-# FOREIGN GHC import Control.Concurrent #-}
{-# FOREIGN GHC import Data.Text (pack) #-}
{-# COMPILE GHC ThreadId = type ThreadId #-}
{-# COMPILE GHC primEqThreadId = \ t1 t2 -> t1 == t2 #-}
{-# COMPILE GHC primLessThanThreadId = \ t1 t2 -> t1 < t2 #-}
{-# COMPILE GHC primShowThreadId = \ t -> pack (show t) #-}

-------------------------------------------------------------------------------
-- Base (IO API)
-------------------------------------------------------------------------------

module Base where

  postulate
    myThreadId : IO ThreadId
    forkIO : IO Unit -> IO ThreadId
    killThread : ThreadId -> IO Unit
    yield : IO Unit
    threadDelay : Nat -> IO Unit

  {-# FOREIGN GHC import Control.Concurrent #-}
  {-# COMPILE GHC forkIO = forkIO #-}
  {-# COMPILE GHC killThread = killThread #-}
  {-# COMPILE GHC yield = yield #-}
  {-# COMPILE GHC threadDelay = \ t -> threadDelay (fromInteger t) #-}

-------------------------------------------------------------------------------
-- Improved API
-------------------------------------------------------------------------------

module _ {{_ : MonadIO m}} where

  myThreadId : m ThreadId
  myThreadId = liftIO (Base.myThreadId)

  killThread : ThreadId -> m Unit
  killThread = liftIO <<< Base.killThread

  yield : m Unit
  yield = liftIO (Base.yield)

  threadDelay : {{_ : TimeUnit a}} -> a -> m Unit
  threadDelay = liftIO <<< Base.threadDelay <<< toMicroseconds

forkIO : {{_ : MonadUnliftIO m}} -> m Unit -> m ThreadId
forkIO f = withRunInIO \ run -> Base.forkIO (run f)
