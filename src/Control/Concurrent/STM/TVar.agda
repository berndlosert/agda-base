{-# OPTIONS --type-in-type #-}

module Control.Concurrent.STM.TVar where

open import Prelude

open import Control.Monad.STM

private variable a s : Set

postulate
  TVar : Set -> Set
  newSTM : a -> STM (TVar a)
  newIO : a -> IO (TVar a)
  readSTM : TVar a -> STM a
  readIO : TVar a -> IO a
  write : TVar a -> a -> STM Unit
  modify : TVar a -> (a -> a) -> STM Unit
  state : TVar s -> (s -> a * s) -> STM a
  switch : TVar a -> a -> STM a
  registerDelay : Nat -> IO (TVar Bool)

private
  postulate
    primEqTVar : TVar a -> TVar a -> Bool

instance
  eqTVar : Eq (TVar a)
  eqTVar ._==_ = primEqTVar

{-# FOREIGN GHC import Control.Concurrent.STM.TVar #-}
{-# COMPILE GHC TVar = type TVar #-}
{-# COMPILE GHC primEqTVar = \ _ v1 v2 -> v1 == v2 #-}
{-# COMPILE GHC newSTM = \ _ x -> newTVar x #-}
{-# COMPILE GHC newIO = \ _ x -> newTVarIO x #-}
{-# COMPILE GHC readSTM = \ _ v -> readTVar v #-}
{-# COMPILE GHC readIO = \ _ v -> readTVarIO v #-}
{-# COMPILE GHC write = \ _ v x -> writeTVar v x #-}
{-# COMPILE GHC modify = \ _ v f -> modifyTVar' v f #-}
{-# COMPILE GHC state = \ _ v f -> stateTVar v f #-}
{-# COMPILE GHC switch = \ _ v x -> swapTVar v x #-}
{-# COMPILE GHC registerDelay = \ _ n -> registerDelay (fromIntegral n) #-}
