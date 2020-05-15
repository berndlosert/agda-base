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
  constructor contT:
  field runContT : (A -> M R) -> M R

open ContT public

evalContT : {{_ : Monad M}} -> ContT R M R -> M R
evalContT (contT: m) = m return

mapContT : (M R -> M R) -> ContT R M ~> ContT R M
mapContT f (contT: m) = contT: (f ∘ m)

withContT : ((B -> M R) -> (A -> M R)) -> ContT R M A -> ContT R M B
withContT f (contT: m) = contT: (m ∘ f)

instance
  functorContT : Functor (ContT R M)
  functorContT .map f (contT: m) = contT: λ c -> m (c ∘ f)

  applicativeContT : Applicative (ContT R M)
  applicativeContT .pure x = contT: (_$ x)
  applicativeContT ._<*>_ (contT: f) (contT: x) =
    contT: λ c -> f λ g -> x (c ∘ g)

  monadContT : Monad (ContT R M)
  monadContT ._>>=_ (contT: m) k = contT: λ c -> m λ x -> runContT (k x) c

  monadTransContT : MonadTrans (ContT R)
  monadTransContT .lift m = contT: (m >>=_)
  monadTransContT .tmap f g (contT: h) = contT: λ k -> f (h (g ∘ k))

  monadContContT : MonadCont (ContT R M)
  monadContContT .callCC f =
    contT: λ c -> runContT (f λ x -> contT: λ _ -> c x) c

  monadBaseContT : {{_ : Monad M}} {{_ : Monad N}} {{_ : MonadBase M N}}
    -> MonadBase M (ContT R N)
  monadBaseContT .liftBase m = lift (liftBase m)

resetT : {{_ : Monad M}} -> ContT R M R -> ContT R' M R
resetT = lift ∘ evalContT

shiftT : {{_ : Monad M}} -> ((A -> M R) -> ContT R M R) -> ContT R M A
shiftT f = contT: (evalContT ∘ f)

liftLocal : {{_ : Monad M}}
  -> M R' -> ((R' -> R') -> M R -> M R)
  -> (R' -> R') -> ContT R M ~> ContT R M
liftLocal ask local f (contT: m) = contT: λ c -> do
  r <- ask
  local f (m (local (const r) ∘ c))
