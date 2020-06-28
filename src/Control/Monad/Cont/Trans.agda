{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Cont.Class
open import Control.Monad.Trans.Class

private
  variable
    a b r r' : Set
    f m n : Set -> Set

record ContT (r : Set) (m : Set -> Set) (a : Set) : Set where
  constructor ContT:
  field runContT : (a -> m r) -> m r

open ContT public

evalContT : {{_ : Monad m}} -> ContT r m r -> m r
evalContT (ContT: m) = m return

mapContT : (m r -> m r) -> ContT r m ~> ContT r m
mapContT f (ContT: m) = ContT: (f ∘ m)

withContT : ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b
withContT f (ContT: m) = ContT: (m ∘ f)

instance
  functorContT : Functor (ContT r m)
  functorContT .map f (ContT: m) = ContT: λ c -> m (c ∘ f)

  applicativeContT : Applicative (ContT r m)
  applicativeContT .pure x = ContT: (_$ x)
  applicativeContT ._<*>_ (ContT: f) (ContT: x) =
    ContT: λ c -> f λ g -> x (c ∘ g)

  monadContT : Monad (ContT r m)
  monadContT ._>>=_ (ContT: m) k = ContT: λ c -> m λ x -> runContT (k x) c

  monadTransContT : MonadTrans (ContT r)
  monadTransContT .lift m = ContT: (m >>=_)
  monadTransContT .tmap f g (ContT: h) = ContT: λ k -> f (h (g ∘ k))

  monadContContT : MonadCont (ContT r n)
  monadContContT .callCC f =
    ContT: λ c -> runContT (f λ x -> ContT: λ _ -> c x) c

  monadBaseContT : {{_ : Monad m}} {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (ContT r n)
  monadBaseContT .liftBase m = lift (liftBase m)

resetT : {{_ : Monad m}} -> ContT r m r -> ContT r' m r
resetT = lift ∘ evalContT

shiftT : {{_ : Monad m}} -> ((a -> m r) -> ContT r m r) -> ContT r m a
shiftT f = ContT: (evalContT ∘ f)

liftLocal : {{_ : Monad m}}
  -> m r' -> ((r' -> r') -> m r -> m r)
  -> (r' -> r') -> ContT r m ~> ContT r m
liftLocal ask local f (ContT: m) = ContT: λ c -> do
  r <- ask
  local f (m (local (const r) ∘ c))
