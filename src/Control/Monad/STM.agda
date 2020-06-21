{-# OPTIONS --type-in-type #-}

module Control.Monad.STM where

open import Prelude

private variable A B : Set

postulate
  STM : Set -> Set
  atomically : STM A -> IO A
  retry : STM A
  orElse : STM A -> STM A -> STM A
  check : Bool -> STM Unit

private
  postulate
    mapSTM : (A -> B) -> STM A -> STM B
    pureSTM : A -> STM A
    apSTM : STM (A -> B) -> STM A -> STM B
    bindSTM : STM A -> (A -> STM B) -> STM B

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
{-# COMPILE GHC mapSTM = \ _ _ f -> map f #-}
{-# COMPILE GHC pureSTM = \ _ x -> pure x #-}
{-# COMPILE GHC apSTM = \ _ _ f x -> f <*> x #-}
{-# COMPILE GHC bindSTM = \ _ _ m k -> m >>= k #-}
