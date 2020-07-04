{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer where

open import Prelude

open import Control.Monad.Writer.Class public
open import Control.Monad.Writer.Trans public

private variable a b w w' : Set

Writer : Set -> Set -> Set
Writer W = WriterT W Identity

writer: : a * w -> Writer w a
writer: = WriterT: ∘ Identity:

runWriter : Writer w a -> a * w
runWriter = runIdentity ∘ runWriterT

execWriter : Writer w a -> w
execWriter m = snd (runWriter m)

mapWriter : (a * w -> b * w') -> Writer w a -> Writer w' b
mapWriter = mapWriterT ∘ map
