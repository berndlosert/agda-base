module Control.Monad.Cont.Trans where

open import Prelude

open import Control.Monad.Base public
open import Control.Monad.Cont.Class public
open import Control.Monad.Trans.Class public

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
  FunctorContT : Functor (ContT r m)
  FunctorContT .map f (ContT: m) = ContT: λ c -> m (c ∘ f)

  ApplicativeContT : Applicative (ContT r m)
  ApplicativeContT .pure x = ContT: (_$ x)
  ApplicativeContT ._<*>_ (ContT: f) (ContT: x) =
    ContT: λ c -> f λ g -> x (c ∘ g)

  MonadContT : Monad (ContT r m)
  MonadContT ._>>=_ (ContT: m) k = ContT: λ c -> m λ x -> runContT (k x) c

  MonadTransContT : MonadTrans (ContT r)
  MonadTransContT .lift m = ContT: (m >>=_)

  MonadContContT : MonadCont (ContT r n)
  MonadContContT .callCC f =
    ContT: λ c -> runContT (f λ x -> ContT: λ _ -> c x) c

  MonadBaseContT : {{_ : Monad m}} {{_ : Monad n}} {{_ : MonadBase m n}}
    -> MonadBase m (ContT r n)
  MonadBaseContT .liftBase m = lift (liftBase m)

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
