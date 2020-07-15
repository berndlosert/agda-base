{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader.Trans where

open import Prelude

open import Control.Monad.Base public
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
mapReaderT f (ReaderT: m) = ReaderT: (f ∘ m)

withReaderT : (r' -> r) -> ReaderT r m ~> ReaderT r' m
withReaderT f (ReaderT: m) = ReaderT: (m ∘ f)

instance
  functorReaderT : {{_ : Functor m}} -> Functor (ReaderT r m)
  functorReaderT .map f = mapReaderT (map f)

  applicativeReaderT : {{_ : Applicative m}} -> Applicative (ReaderT r m)
  applicativeReaderT .pure = ReaderT: ∘ const ∘ pure
  applicativeReaderT ._<*>_ (ReaderT: f) (ReaderT: x) = ReaderT: λ r ->
    f r <*> x r

  monadReaderT : {{_ : Monad m}} -> Monad (ReaderT r m)
  monadReaderT ._>>=_ (ReaderT: m) k = ReaderT: λ r -> do
    a <- m r
    runReaderT (k a) r

  monadReaderReaderT : {{_ : Monad m}} -> MonadReader r (ReaderT r m)
  monadReaderReaderT .ask = ReaderT: return
  monadReaderReaderT .local f = withReaderT f

  mfunctorReaderT : MFunctor (ReaderT r)
  mfunctorReaderT .hoist t = mapReaderT t

  monadTransReaderT : MonadTrans (ReaderT r)
  monadTransReaderT .lift = ReaderT: ∘ const

  mmonadReaderT : MMonad (ReaderT r)
  mmonadReaderT .embed k (ReaderT: f) = ReaderT: λ r -> runReaderT (k (f r)) r

  monadBaseReaderT : {{_ : Monad m}} {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (ReaderT r n)
  monadBaseReaderT .liftBase m = lift (liftBase m)
