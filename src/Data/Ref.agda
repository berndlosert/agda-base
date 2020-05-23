{-# OPTIONS --type-in-type #-}

module Data.Ref where

open import Prelude

private variable A B : Set

postulate
  Ref : Set -> Set
  new : A -> IO (Ref A)
  read : Ref A -> IO A
  write : Ref A -> A -> IO Unit
  modify : Ref A -> (A -> A) -> IO Unit
  atomicModify : Ref A -> (A -> A * B) -> IO B
  atomicWrite : Ref A -> A -> IO Unit

{-# FOREIGN GHC import Data.IORef #-}
{-# COMPILE GHC Ref = type IORef #-}
{-# COMPILE GHC new = \ _ x -> newIORef x #-}
{-# COMPILE GHC read = \ _ r -> readIORef r #-}
{-# COMPILE GHC write = \ _ r x -> writeIORef r x #-}
{-# COMPILE GHC modify = \ _ r f -> modifyIORef' r f #-}
{-# COMPILE GHC atomicModify = \ _ _ r f -> atomicModifyIORef' r f #-}
{-# COMPILE GHC atomicWrite = \ _ r x -> atomicWriteIORef r x #-}
