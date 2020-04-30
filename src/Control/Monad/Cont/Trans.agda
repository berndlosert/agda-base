{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont.Trans where

open import Prelude

open import Control.Monad.Cont.Class
open import Control.Monad.Trans.Class

private
  variable
    A B R R' : Set
    F M : Set -> Set

record ContT (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor contT:
  field runContT : (A -> M R) -> M R

open ContT public

evalContT : {{_ : Monad M}} -> ContT R M R -> M R
evalContT m = runContT m return

mapContT : (M R -> M R) -> ContT R M ~> ContT R M
mapContT f m = contT: (f ∘ runContT m)

withContT : ((B -> M R) -> (A -> M R)) -> ContT R M A -> ContT R M B
withContT f m = contT: (runContT m ∘ f)

instance
  functorContT : Functor (ContT R M)
  functorContT .map f m = contT: λ c -> runContT m (c ∘ f)

  applicativeContT : Applicative (ContT R M)
  applicativeContT .pure x = contT: (_$ x)
  applicativeContT ._<*>_ f v =
    contT: λ c -> runContT f λ g -> runContT v (c ∘ g)

  monadContT : Monad (ContT R M)
  monadContT ._>>=_ m k = contT: λ c -> runContT m (λ x -> runContT (k x) c)

  monadTransContT : MonadTrans (ContT R)
  monadTransContT .lift m = contT: (m >>=_)
  monadTransContT .transform = monadContT

  monadContContT : MonadCont (ContT R M)
  monadContContT .callCC f =
    contT: λ c -> runContT (f (λ x -> contT: λ _ -> c x)) c

resetT : {{_ : Monad M}} -> ContT R M R -> ContT R' M R
resetT = lift ∘ evalContT

shiftT : {{_ : Monad M}} -> ((A -> M R) -> ContT R M R) -> ContT R M A
shiftT f = contT: (evalContT ∘ f)

liftLocal : {{_ : Monad M}}
  -> M R' -> ((R' -> R') -> M R -> M R)
  -> (R' -> R') -> ContT R M ~> ContT R M
liftLocal ask local f m = contT: λ c -> do
    r <- ask
    local f (runContT m (local (const r) ∘ c))
