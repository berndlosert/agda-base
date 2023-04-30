module Data.IORef where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- IORef
-------------------------------------------------------------------------------

postulate
  IORef : Type -> Type
  newIORef : a -> IO (IORef a)
  readIORef : IORef a -> IO a
  writeIORef : IORef a -> a -> IO Unit
  modifyIORef : IORef a -> (a -> a) -> IO Unit
  atomicModifyIORef : IORef a -> (a -> Tuple a b) -> IO b
  atomicWriteIORef : IORef a -> a -> IO Unit

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.IORef #-}
{-# COMPILE GHC IORef = type IORef #-}
{-# COMPILE GHC newIORef = \ _ x -> newIORef x #-}
{-# COMPILE GHC readIORef = \ _ r -> readIORef r #-}
{-# COMPILE GHC writeIORef = \ _ r x -> writeIORef r x #-}
{-# COMPILE GHC modifyIORef = \ _ r f -> modifyIORef' r f #-}
{-# COMPILE GHC atomicModifyIORef = \ _ _ r f -> atomicModifyIORef' r f #-}
{-# COMPILE GHC atomicWriteIORef = \ _ r x -> atomicWriteIORef r x #-}
