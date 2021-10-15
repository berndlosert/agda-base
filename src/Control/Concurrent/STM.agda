{-# OPTIONS --type-in-type #-}

module Control.Concurrent.STM where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b s : Set

-------------------------------------------------------------------------------
-- STM
-------------------------------------------------------------------------------

postulate
  STM : Set -> Set
  atomically : STM a -> IO a
  retry : STM a
  orElse : STM a -> STM a -> STM a
  check : Bool -> STM Unit

private
  postulate
    mapSTM : (a -> b) -> STM a -> STM b
    pureSTM : a -> STM a
    apSTM : STM (a -> b) -> STM a -> STM b
    bindSTM : STM a -> (a -> STM b) -> STM b

instance
  Functor-STM : Functor STM
  Functor-STM .map = mapSTM

  Applicative-STM : Applicative STM
  Applicative-STM .pure = pureSTM
  Applicative-STM ._<*>_ = apSTM

  Alternative-STM : Alternative STM
  Alternative-STM .azero = retry
  Alternative-STM ._<|>_ = orElse

  Monad-STM : Monad STM
  Monad-STM ._>>=_ = bindSTM

{-# FOREIGN GHC import Control.Monad.STM #-}
{-# COMPILE GHC STM = type STM #-}
{-# COMPILE GHC atomically = \ _ stm -> atomically stm #-}
{-# COMPILE GHC retry = \ _ -> retry #-}
{-# COMPILE GHC orElse = \ _ stm1 stm2 -> stm1 `orElse` stm2 #-}
{-# COMPILE GHC mapSTM = \ _ _ f x -> fmap f x #-}
{-# COMPILE GHC pureSTM = \ _ x -> pure x #-}
{-# COMPILE GHC apSTM = \ _ _ f x -> f <*> x #-}
{-# COMPILE GHC bindSTM = \ _ _ m k -> m >>= k #-}

-------------------------------------------------------------------------------
-- TVar
-------------------------------------------------------------------------------

postulate
  TVar : Set -> Set
  newTVar : a -> STM (TVar a)
  newTVarIO : a -> IO (TVar a)
  readTVar : TVar a -> STM a
  readTVarIO : TVar a -> IO a
  writeTVar : TVar a -> a -> STM Unit
  modifyTVar : TVar a -> (a -> a) -> STM Unit
  stateTVar : TVar s -> (s -> Pair a s) -> STM a
  swapTVar : TVar a -> a -> STM a
  registerDelay : Nat -> IO (TVar Bool)

private
  postulate
    tvarEq : TVar a -> TVar a -> Bool

instance
  Eq-TVar : Eq (TVar a)
  Eq-TVar ._==_ = tvarEq

{-# FOREIGN GHC import Control.Concurrent.STM.TVar #-}
{-# COMPILE GHC TVar = type TVar #-}
{-# COMPILE GHC tvarEq = \ _ v1 v2 -> v1 == v2 #-}
{-# COMPILE GHC newTVar = \ _ x -> newTVar x #-}
{-# COMPILE GHC newTVarIO = \ _ x -> newTVarIO x #-}
{-# COMPILE GHC readTVar = \ _ v -> readTVar v #-}
{-# COMPILE GHC readTVarIO = \ _ v -> readTVarIO v #-}
{-# COMPILE GHC writeTVar = \ _ v x -> writeTVar v x #-}
{-# COMPILE GHC modifyTVar = \ _ v f -> modifyTVar' v f #-}
{-# COMPILE GHC stateTVar = \ _ _ v f -> stateTVar v f #-}
{-# COMPILE GHC swapTVar = \ _ v x -> swapTVar v x #-}
{-# COMPILE GHC registerDelay = \ n -> registerDelay (fromIntegral n) #-}

-------------------------------------------------------------------------------
-- TMVar
-------------------------------------------------------------------------------

postulate
  TMVar : Set -> Set
  newTMVar : a -> STM (TMVar a)
  newEmptyTMVar : STM (TMVar a)
  newTMVarIO : a -> IO (TMVar a)
  newEmptyTMVarIO : IO (TMVar a)
  takeTMVar : TMVar a -> STM a
  putTMVar : TMVar a -> a -> STM Unit
  readTMVar : TMVar a -> STM a
  tryReadTMVar : TMVar a -> STM (Maybe a)
  swapTMVar : TMVar a -> a -> STM a
  tryTakeTMVar : TMVar a -> STM (Maybe a)
  tryPutTMVar : TMVar a -> a -> STM Bool
  isEmptyTMVar : TMVar a -> STM Bool

private
  postulate
    primEqTMVar : TMVar a -> TMVar a -> Bool

instance
  Eq-TMVar : Eq (TMVar a)
  Eq-TMVar ._==_ = primEqTMVar

{-# FOREIGN GHC import Control.Concurrent.STM.TMVar #-}
{-# COMPILE GHC TMVar = type TMVar #-}
{-# COMPILE GHC primEqTMVar = \ _ v1 v2 -> v1 == v2 #-}
{-# COMPILE GHC newTMVar = \ _ x -> newTMVar x #-}
{-# COMPILE GHC newEmptyTMVar = \ _ -> newEmptyTMVar #-}
{-# COMPILE GHC newTMVarIO = \ _ x -> newTMVarIO x #-}
{-# COMPILE GHC newEmptyTMVarIO = \ _ -> newEmptyTMVarIO #-}
{-# COMPILE GHC takeTMVar = \ _ v -> takeTMVar v #-}
{-# COMPILE GHC putTMVar = \ _ v a -> putTMVar v a #-}
{-# COMPILE GHC readTMVar = \ _ v -> readTMVar v #-}
{-# COMPILE GHC tryReadTMVar = \ _ v -> tryReadTMVar v #-}
{-# COMPILE GHC swapTMVar = \ _ v a -> swapTMVar v a #-}
{-# COMPILE GHC tryTakeTMVar = \ _ v -> tryTakeTMVar v #-}
{-# COMPILE GHC tryPutTMVar = \ _ v a -> tryPutTMVar v a #-}
{-# COMPILE GHC isEmptyTMVar = \ _ v -> isEmptyTMVar v #-}

-------------------------------------------------------------------------------
-- TChan
-------------------------------------------------------------------------------

postulate
  TChan : Set -> Set
  newTChan : STM (TChan a)
  newTChanIO : IO (TChan a)
  newBroadcastTChan : STM (TChan a)
  newBroadcastTChanIO : IO (TChan a)
  dupTChan : TChan a -> STM (TChan a)
  cloneTChan : TChan a -> STM (TChan a)
  readTChan : TChan a -> STM a
  tryReadTChan : TChan a -> STM (Maybe a)
  peekTChan : TChan a -> STM a
  tryPeekTChan : TChan a -> STM (Maybe a)
  writeTChan : TChan a -> a -> STM Unit
  unGetTChan : TChan a -> a -> STM Unit
  isEmptyTChan : TChan a -> STM Bool

{-# FOREIGN GHC import Control.Concurrent.STM.TChan #-}
{-# COMPILE GHC TChan = type TChan #-}
{-# COMPILE GHC newTChan = \ _ -> newTChan #-}
{-# COMPILE GHC newTChanIO = \ _ -> newTChanIO #-}
{-# COMPILE GHC newBroadcastTChan = \ _ -> newBroadcastTChan #-}
{-# COMPILE GHC newBroadcastTChanIO = \ _ -> newBroadcastTChanIO #-}
{-# COMPILE GHC dupTChan = \ _ c -> dupTChan c #-}
{-# COMPILE GHC cloneTChan = \ _ c -> cloneTChan c #-}
{-# COMPILE GHC readTChan = \ _ c -> readTChan c #-}
{-# COMPILE GHC tryReadTChan = \ _ c -> tryReadTChan c #-}
{-# COMPILE GHC peekTChan = \ _ c -> peekTChan c #-}
{-# COMPILE GHC tryPeekTChan = \ _ c -> tryPeekTChan c #-}
{-# COMPILE GHC writeTChan = \ _ c x -> writeTChan c x #-}
{-# COMPILE GHC unGetTChan = \ _ c x -> unGetTChan c x #-}
{-# COMPILE GHC isEmptyTChan = \ _ c -> isEmptyTChan c #-}
