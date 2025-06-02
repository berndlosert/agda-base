module Data.STRef where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.ST

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b s : Type

-------------------------------------------------------------------------------
-- STRef
-------------------------------------------------------------------------------

postulate
  STRef : Type -> Type -> Type
  newSTRef : a -> ST s (STRef s a)
  readSTRef : STRef s a -> ST s a
  writeSTRef : STRef s a -> a -> ST s Unit
  modifySTRef : STRef s a -> (a -> a) -> ST s Unit

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.STRef #-}
{-# COMPILE GHC STRef = type STRef #-}
{-# COMPILE GHC newSTRef = \ _ _ -> newSTRef #-}
{-# COMPILE GHC readSTRef = \ _ _ -> readSTRef #-}
{-# COMPILE GHC writeSTRef = \ _ _ r -> writeSTRef r #-}
{-# COMPILE GHC modifySTRef = \ _ _ r -> modifySTRef' r #-}
