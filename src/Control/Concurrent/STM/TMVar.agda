{-# OPTIONS --type-in-type #-}

module Control.Concurrent.STM.TMVar where

open import Prelude
  hiding (swap)

open import Control.Monad.STM

private variable a s : Set

postulate
  TMVar : Set -> Set
  newSTM : a -> STM (TMVar a)
  newEmptySTM : STM (TMVar a)
  newIO : a -> IO (TMVar a)
  newEmptyIO : STM (TMVar a)
  take : TMVar a -> STM a
  put : TMVar a -> a -> STM Unit
  read : TMVar a -> STM a
  tryRead : TMVar a -> STM (Maybe a)
  swap : TMVar a -> a -> STM a
  tryTake : TMVar a -> STM (Maybe a)
  tryPut : TMVar a -> a -> STM Bool
  isEmpty : TMVar a -> STM Bool

private
  postulate
    primEqTMVar : TMVar a -> TMVar a -> Bool

instance
  eqTMVar : Eq (TMVar a)
  eqTMVar ._==_ = primEqTMVar

{-# FOREIGN GHC import Control.Concurrent.STM.TMVar #-}
{-# COMPILE GHC TMVar = type TMVar #-}
{-# COMPILE GHC primEqTMVar = \ _ v1 v2 -> v1 == v2 #-}
{-# COMPILE GHC newSTM = \ _ x -> newTMVar x #-}
{-# COMPILE GHC newEmptySTM = \ _ -> newEmptyTMVar #-}
{-# COMPILE GHC newIO = \ _ x -> newTMVarIO x #-}
{-# COMPILE GHC newEmptyIO = \ _ -> newEmptyTMVarIO #-}
{-# COMPILE GHC take = \ _ v -> takeTMVar v #-}
{-# COMPILE GHC put = \ _ v a -> putTMVar v a #-}
{-# COMPILE GHC read = \ _ v -> readTMVar v #-}
{-# COMPILE GHC tryRead = \ _ v -> tryReadTMVar v #-}
{-# COMPILE GHC swap = \ _ v a -> swapTMVar v a #-}
{-# COMPILE GHC tryTake = \ _ v -> tryTakeMVar v a #-}
{-# COMPILE GHC tryPut = \ _ v a -> tryPutMVar v a #-}
{-# COMPILE GHC isEmpty = \ _ v -> isEmptyMVar v #-}
