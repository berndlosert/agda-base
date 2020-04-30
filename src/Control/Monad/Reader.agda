{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

open import Prelude

private variable A B R R' : Set

open import Control.Monad.Reader.Trans

Reader : Set -> Set -> Set
Reader R = ReaderT R Identity

aReader : (R -> A) -> Reader R A
aReader f = aReaderT (anIdentity ∘ f)

runReader : Reader R A -> R -> A
runReader m = runIdentity ∘ runReaderT m

mapReader : (A -> B) -> Reader R A -> Reader R B
mapReader f = mapReaderT (anIdentity ∘ f ∘ runIdentity)

withReader : (R' -> R) -> Reader R A -> Reader R' A
withReader f m = withReaderT f m
