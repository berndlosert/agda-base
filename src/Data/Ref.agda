{-# OPTIONS --type-in-type #-}

module Data.Ref where

open import Prelude

private variable a b : Set

postulate
  Ref : Set -> Set
  new : a -> IO (Ref a)
  read : Ref a -> IO a
  write : Ref a -> a -> IO Unit
  modify : Ref a -> (a -> a) -> IO Unit
  atomicModify : Ref a -> (a -> a * b) -> IO b
  atomicWrite : Ref a -> a -> IO Unit

{-# FOREIGN GHC import Data.IORef #-}
{-# COMPILE GHC Ref = type IORef #-}
{-# COMPILE GHC new = \ _ x -> newIORef x #-}
{-# COMPILE GHC read = \ _ r -> readIORef r #-}
{-# COMPILE GHC write = \ _ r x -> writeIORef r x #-}
{-# COMPILE GHC modify = \ _ r f -> modifyIORef' r f #-}
{-# COMPILE GHC atomicModify = \ _ _ r f -> atomicModifyIORef' r f #-}
{-# COMPILE GHC atomicWrite = \ _ r x -> atomicWriteIORef r x #-}
