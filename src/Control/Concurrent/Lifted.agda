{-# OPTIONS --type-in-type #-}

module Control.Concurrent.Lifted where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Concurrent as Base using ()
open import Control.Monad.IO.Class
open import Control.Monad.IO.Unlift
open import Data.Time.Units

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Base public
  using (ThreadId; Eq-ThreadId; Ord-ThreadId; Show-ThreadId)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    m : Set -> Set

-------------------------------------------------------------------------------
-- Lifted functions
-------------------------------------------------------------------------------

module _ {{_ : MonadIO m}} where

  myThreadId : m ThreadId
  myThreadId = liftIO Base.myThreadId

  killThread : ThreadId -> m Unit
  killThread = liftIO <<< Base.killThread

  yield : m Unit
  yield = liftIO Base.yield

  threadDelay : {{_ : TimeUnit a}} -> a -> m Unit
  threadDelay = liftIO <<< Base.threadDelay

forkIO : {{_ : MonadUnliftIO m}} -> m Unit -> m ThreadId
forkIO f = withRunInIO \ run -> Base.forkIO (run f)
