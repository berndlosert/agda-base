{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Cont where

open import Prelude

open import Control.Monad.Trans.Class
  using (MonadTrans; lift; transform)

private
  variable
    A B R R' : Set
    F M : Set -> Set

--------------------------------------------------------------------------------
-- MonadCont
--------------------------------------------------------------------------------

record MonadCont (M : Set -> Set) : Set where
  field
    {{monad}} : Monad M
    callCC : ((A -> M B) -> M A) -> M A

open MonadCont {{...}} public

--------------------------------------------------------------------------------
-- ContT
--------------------------------------------------------------------------------

record ContT (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor aContT
  field
    runContT : (A -> M R) -> M R

open ContT public

evalContT : {{_ : Monad M}} -> ContT R M R -> M R
evalContT m = runContT m return

mapContT : (M R -> M R) -> ContT R M ~> ContT R M
mapContT f m = aContT $ f ∘ runContT m

withContT : ((B -> M R) -> (A -> M R)) -> ContT R M A -> ContT R M B
withContT f m = aContT $ runContT m ∘ f

instance
  functorContT : Functor (ContT R M)
  functorContT .map f m = aContT λ c -> runContT m (c ∘ f)

  applicativeContT : Applicative (ContT R M)
  applicativeContT .pure x = aContT (_$ x)
  applicativeContT ._<*>_ f v =
    aContT λ c -> runContT f $ λ g -> runContT v (c ∘ g)

  monadContT : Monad (ContT R M)
  monadContT ._>>=_ m k = aContT $ λ c -> runContT m (λ x -> runContT (k x) c)

  monadTransContT : MonadTrans (ContT R)
  monadTransContT .lift m = aContT (m >>=_)
  monadTransContT .transform = monadContT

  monadContContT : MonadCont (ContT R M)
  monadContContT .callCC f =
    aContT $ λ c -> runContT (f (λ x -> aContT $ λ _ -> c x)) c

resetT : {{_ : Monad M}} -> ContT R M R -> ContT R' M R
resetT = lift ∘ evalContT

shiftT : {{_ : Monad M}} -> ((A -> M R) -> ContT R M R) -> ContT R M A
shiftT f = aContT (evalContT ∘ f)

liftLocal : {{_ : Monad M}}
  -> M R' -> ((R' -> R') -> M R -> M R)
  -> (R' -> R') -> ContT R M ~> ContT R M
liftLocal ask local f m = aContT $ λ c -> do
    r <- ask
    local f (runContT m (local (const r) ∘ c))

--------------------------------------------------------------------------------
-- Cont
--------------------------------------------------------------------------------

Cont : Set -> Set -> Set
Cont R A = ContT R Identity A

aCont : ((A -> R) -> R) -> Cont R A
aCont f = aContT (λ c -> anIdentity (f (runIdentity ∘ c)))

runCont : Cont R A -> (A -> R) -> R
runCont m k = runIdentity (runContT m (anIdentity ∘ k))

evalCont : Cont R R -> R
evalCont m = runIdentity (evalContT m)

mapCont : (R -> R) -> Cont R A -> Cont R A
mapCont f = mapContT (map f)

withCont : ((B -> R) -> (A -> R)) -> Cont R A -> Cont R B
withCont f = withContT ((anIdentity ∘_) ∘ f ∘ (runIdentity ∘_))

reset : Cont R R -> Cont R' R
reset = resetT

shift : ((A -> R) -> Cont R R) -> Cont R A
shift f = shiftT (f ∘ (runIdentity ∘_))
