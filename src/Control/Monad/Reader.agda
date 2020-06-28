{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

open import Prelude

private variable a b r r' : Set

open import Control.Monad.Reader.Trans

open Control.Monad.Reader.Trans public
  using (functorReaderT; applicativeReaderT; monadReaderT)

Reader : Set -> Set -> Set
Reader r = ReaderT r Identity

reader : (r -> a) -> Reader r a
reader f = ReaderT: (Identity: ∘ f)

runReader : Reader r a -> r -> a
runReader m = runIdentity ∘ runReaderT m

mapReader : (a -> b) -> Reader r a -> Reader r b
mapReader f = mapReaderT (Identity: ∘ f ∘ runIdentity)

withReader : (r' -> r) -> Reader r a -> Reader r' a
withReader f m = withReaderT f m
