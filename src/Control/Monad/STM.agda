{-# OPTIONS --type-in-type #-}

module Control.Monad.STM where

open import Prelude

private variable a b : Set

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
  functorSTM : Functor STM
  functorSTM .map = mapSTM

  applicativeSTM : Applicative STM
  applicativeSTM .pure = pureSTM
  applicativeSTM ._<*>_ = apSTM

  alternativeSTM : Alternative STM
  alternativeSTM .empty = retry
  alternativeSTM ._<|>_ = orElse

  monadSTM : Monad STM
  monadSTM ._>>=_ = bindSTM

{-# FOREIGN GHC import Control.Monad.STM #-}
{-# COMPILE GHC STM = type STM #-}
{-# COMPILE GHC atomically = \ _ stm -> atomically stm #-}
{-# COMPILE GHC retry = \ _ -> retry #-}
{-# COMPILE GHC orElse = \ _ stm1 stm2 -> stm1 `orElse` stm2 #-}
{-# COMPILE GHC mapSTM = \ _ _ f x -> fmap f x #-}
{-# COMPILE GHC pureSTM = \ _ x -> pure x #-}
{-# COMPILE GHC apSTM = \ _ _ f x -> f <*> x #-}
{-# COMPILE GHC bindSTM = \ _ _ m k -> m >>= k #-}
