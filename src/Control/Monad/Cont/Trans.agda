{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Cont.Class
open import Control.Monad.Trans.Class

private
  variable
    A B R R' : Set
    F M N : Set -> Set

record ContT (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor ContT:
  field runContT : (A -> M R) -> M R

open ContT public

evalContT : {{_ : Monad M}} -> ContT R M R -> M R
evalContT (ContT: m) = m return

mapContT : (M R -> M R) -> ContT R M ~> ContT R M
mapContT f (ContT: m) = ContT: (f ∘ m)

withContT : ((B -> M R) -> (A -> M R)) -> ContT R M A -> ContT R M B
withContT f (ContT: m) = ContT: (m ∘ f)

instance
  functorContT : Functor (ContT R M)
  functorContT .map f (ContT: m) = ContT: λ c -> m (c ∘ f)

  applicativeContT : Applicative (ContT R M)
  applicativeContT .pure x = ContT: (_$ x)
  applicativeContT ._<*>_ (ContT: f) (ContT: x) =
    ContT: λ c -> f λ g -> x (c ∘ g)

  monadContT : Monad (ContT R M)
  monadContT ._>>=_ (ContT: m) k = ContT: λ c -> m λ x -> runContT (k x) c

  monadTransContT : MonadTrans (ContT R)
  monadTransContT .lift m = ContT: (m >>=_)
  monadTransContT .tmap f g (ContT: h) = ContT: λ k -> f (h (g ∘ k))

  monadContContT : MonadCont (ContT R M)
  monadContContT .callCC f =
    ContT: λ c -> runContT (f λ x -> ContT: λ _ -> c x) c

  monadBaseContT : {{_ : Monad M}} {{_ : Monad N}} {{_ : MonadBase M N}}
    -> MonadBase M (ContT R N)
  monadBaseContT .liftBase m = lift (liftBase m)

resetT : {{_ : Monad M}} -> ContT R M R -> ContT R' M R
resetT = lift ∘ evalContT

shiftT : {{_ : Monad M}} -> ((A -> M R) -> ContT R M R) -> ContT R M A
shiftT f = ContT: (evalContT ∘ f)

liftLocal : {{_ : Monad M}}
  -> M R' -> ((R' -> R') -> M R -> M R)
  -> (R' -> R') -> ContT R M ~> ContT R M
liftLocal ask local f (ContT: m) = ContT: λ c -> do
  r <- ask
  local f (m (local (const r) ∘ c))
