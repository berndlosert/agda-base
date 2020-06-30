{-# OPTIONS --type-in-type #-}

module Control.Concurrent.STM.TChan where

open import Prelude

open import Control.Monad.STM

private variable a : Set

postulate
  TChan : Set -> Set
  newSTM : STM (TChan a)
  newIO : IO (TChan a)
  newBroadcastSTM : STM (TChan a)
  newBroadcastIO : IO (TChan a)
  dup : TChan a -> STM (TChan a)
  clone : TChan a -> STM (TChan a)
  read : TChan a -> STM a
  tryRead : TChan a -> STM (Maybe a)
  peek : TChan a -> STM a
  tryPeek : TChan a -> STM (Maybe a)
  write : TChan a -> a -> STM Unit
  unget : TChan a -> a -> STM Unit
  isEmpty : TChan a -> STM Bool

{-# FOREIGN GHC import Control.Concurrent.STM.TChan #-}
{-# COMPILE GHC TChan = type TChan #-}
{-# COMPILE GHC newSTM = \ _ -> newTChan #-}
{-# COMPILE GHC newIO = \ _ -> newTChanIO #-}
{-# COMPILE GHC newBroadcastSTM = \ _ -> newBroadcastTChan #-}
{-# COMPILE GHC newBroadcastIO = \ _ -> newBroadcastTChanIO #-}
{-# COMPILE GHC dup = \ _ c -> dupTChan c #-}
{-# COMPILE GHC clone = \ _ c -> cloneTChan c #-}
{-# COMPILE GHC read = \ _ c -> readTChan c #-}
{-# COMPILE GHC tryRead = \ _ c -> tryReadTChan c #-}
{-# COMPILE GHC peek = \ _ c -> peekTChan c #-}
{-# COMPILE GHC tryPeek = \ _ c -> tryPeekTChan c #-}
{-# COMPILE GHC write = \ _ c x -> writeTChan c x #-}
{-# COMPILE GHC unget = \ _ c x -> unGetTChan c x #-}
{-# COMPILE GHC isEmpty = \ _ c -> isEmptyTChan c #-}
