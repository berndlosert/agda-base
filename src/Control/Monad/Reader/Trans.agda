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
  FunctorReaderT : {{_ : Functor m}} -> Functor (ReaderT r m)
  FunctorReaderT .map f = mapReaderT (map f)

  ApplicativeReaderT : {{_ : Applicative m}} -> Applicative (ReaderT r m)
  ApplicativeReaderT .pure = ReaderT: ∘ const ∘ pure
  ApplicativeReaderT ._<*>_ (ReaderT: f) (ReaderT: x) = ReaderT: λ r ->
    f r <*> x r

  MonadReaderT : {{_ : Monad m}} -> Monad (ReaderT r m)
  MonadReaderT ._>>=_ (ReaderT: m) k = ReaderT: λ r -> do
    a <- m r
    runReaderT (k a) r

  MonadReaderReaderT : {{_ : Monad m}} -> MonadReader r (ReaderT r m)
  MonadReaderReaderT .ask = ReaderT: return
  MonadReaderReaderT .local f = withReaderT f

  MFunctorReaderT : MFunctor (ReaderT r)
  MFunctorReaderT .hoist t = mapReaderT t

  MonadTransReaderT : MonadTrans (ReaderT r)
  MonadTransReaderT .lift = ReaderT: ∘ const

  MMonadReaderT : MMonad (ReaderT r)
  MMonadReaderT .embed k (ReaderT: f) = ReaderT: λ r -> runReaderT (k (f r)) r

  MonadBaseReaderT : {{_ : Monad m}} {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (ReaderT r n)
  MonadBaseReaderT .liftBase m = lift (liftBase m)
