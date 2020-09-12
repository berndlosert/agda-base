{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader.Trans where

open import Prelude

open import Control.Monad.Morph public
open import Control.Monad.Reader.Class public
open import Control.Monad.Trans.Class public

private
  variable
    a b r r' : Set
    m n : Set -> Set

record ReaderT (r : Set) (m : Set -> Set) (a : Set) : Set where
  constructor ReaderT:
  field runReaderT : r -> m a

open ReaderT public

mapReaderT : (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f (ReaderT: m) = ReaderT: (f <<< m)

withReaderT : (r' -> r) -> ReaderT r m ~> ReaderT r' m
withReaderT f (ReaderT: m) = ReaderT: (m <<< f)

instance
  Functor-ReaderT : {{_ : Functor m}} -> Functor (ReaderT r m)
  Functor-ReaderT .map f = mapReaderT (map f)

  Applicative-ReaderT : {{_ : Applicative m}} -> Applicative (ReaderT r m)
  Applicative-ReaderT .pure = ReaderT: <<< const <<< pure
  Applicative-ReaderT ._<*>_ (ReaderT: f) (ReaderT: x) = ReaderT: \ r ->
    f r <*> x r

  Monad-ReaderT : {{_ : Monad m}} -> Monad (ReaderT r m)
  Monad-ReaderT ._>>=_ (ReaderT: m) k = ReaderT: \ r -> do
    a <- m r
    runReaderT (k a) r

  MonadReader-ReaderT : {{_ : Monad m}} -> MonadReader r (ReaderT r m)
  MonadReader-ReaderT .ask = ReaderT: return
  MonadReader-ReaderT .local f = withReaderT f

  MFunctor-ReaderT : MFunctor (ReaderT r)
  MFunctor-ReaderT .hoist t = mapReaderT t

  MonadTrans-ReaderT : MonadTrans (ReaderT r)
  MonadTrans-ReaderT .lift = ReaderT: <<< const

  MMonad-ReaderT : MMonad (ReaderT r)
  MMonad-ReaderT .embed k (ReaderT: f) = ReaderT: \ r -> runReaderT (k (f r)) r
