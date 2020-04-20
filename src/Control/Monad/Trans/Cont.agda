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
  constructor toContT
  field
    fromContT : (A -> M R) -> M R

open ContT public

evalContT : {{_ : Monad M}} -> ContT R M R -> M R
evalContT m = fromContT m return

mapContT : (M R -> M R) -> ContT R M ~> ContT R M
mapContT f m = toContT $ f <<< fromContT m

withContT : ((B -> M R) -> (A -> M R)) -> ContT R M A -> ContT R M B
withContT f m = toContT $ fromContT m <<< f

instance
  functorContT : Functor (ContT R M)
  functorContT .map f m = toContT \ c -> fromContT m (c <<< f)

  applicativeContT : Applicative (ContT R M)
  applicativeContT .pure x = toContT (_$ x)
  applicativeContT ._<*>_ f v =
    toContT \ c -> fromContT f $ \ g -> fromContT v (c <<< g)

  monadContT : Monad (ContT R M)
  monadContT ._>>=_ m k = toContT $ \ c -> fromContT m (\ x -> fromContT (k x) c)

  monadTransContT : MonadTrans (ContT R)
  monadTransContT .lift m = toContT (m >>=_)
  monadTransContT .transform = monadContT

  monadContContT : MonadCont (ContT R M)
  monadContContT .callCC f =
    toContT $ \ c -> fromContT (f (\ x -> toContT $ \ _ -> c x)) c

resetT : {{_ : Monad M}} -> ContT R M R -> ContT R' M R
resetT = lift <<< evalContT

shiftT : {{_ : Monad M}} -> ((A -> M R) -> ContT R M R) -> ContT R M A
shiftT f = toContT (evalContT <<< f)

liftLocal : {{_ : Monad M}}
  -> M R' -> ((R' -> R') -> M R -> M R)
  -> (R' -> R') -> ContT R M ~> ContT R M
liftLocal ask local f m = toContT $ \ c -> do
    r <- ask
    local f (fromContT m (local (const r) <<< c))

--------------------------------------------------------------------------------
-- Cont
--------------------------------------------------------------------------------

Cont : Set -> Set -> Set
Cont R A = ContT R Id A

toCont : ((A -> R) -> R) -> Cont R A
toCont f = toContT (\ c -> toId (f (fromId <<< c)))

fromCont : Cont R A -> (A -> R) -> R
fromCont m k = fromId (fromContT m (toId <<< k))

evalCont : Cont R R -> R
evalCont m = fromId (evalContT m)

mapCont : (R -> R) -> Cont R A -> Cont R A
mapCont f = mapContT (map f)

withCont : ((B -> R) -> (A -> R)) -> Cont R A -> Cont R B
withCont f = withContT ((toId <<<_) <<< f <<< (fromId <<<_))

reset : Cont R R -> Cont R' R
reset = resetT

shift : ((A -> R) -> Cont R R) -> Cont R A
shift f = shiftT (f <<< (fromId <<<_))
