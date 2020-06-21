{-# OPTIONS --type-in-type #-}

module Control.Concurrent.STM.TVar where

open import Prelude

open import Control.Monad.STM

private variable A S : Set

postulate
  TVar : Set -> Set
  newSTM : A -> STM (TVar A)
  newIO : A -> IO (TVar A)
  readSTM : TVar A -> STM A
  readIO : TVar A -> IO A
  write : TVar A -> A -> STM Unit
  modify : TVar A -> (A -> A) -> STM Unit
  state : TVar S -> (S -> A * S) -> STM A
  switch : TVar A -> A -> STM A
  registerDelay : Nat -> IO (TVar Bool)

private
  postulate
    primEqTVar : TVar A -> TVar A -> Bool

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
