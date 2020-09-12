{-# OPTIONS --type-in-type #-}

module Control.Monad.Cont.Trans where

open import Prelude

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
mapContT f (ContT: m) = ContT: (f <<< m)

withContT : ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b
withContT f (ContT: m) = ContT: (m <<< f)

instance
  Functor-ContT : Functor (ContT r m)
  Functor-ContT .map f (ContT: m) = ContT: \ c -> m (c <<< f)

  Applicative-ContT : Applicative (ContT r m)
  Applicative-ContT .pure x = ContT: (\ f -> f x)
  Applicative-ContT ._<*>_ (ContT: f) (ContT: x) =
    ContT: \ c -> f \ g -> x (c <<< g)

  Monad-ContT : Monad (ContT r m)
  Monad-ContT ._>>=_ (ContT: m) k = ContT: \ c -> m \ x -> runContT (k x) c

  MonadTrans-ContT : MonadTrans (ContT r)
  MonadTrans-ContT .lift m = ContT: (m >>=_)

  MonadCont-ContT : MonadCont (ContT r n)
  MonadCont-ContT .callCC f =
    ContT: \ c -> runContT (f \ x -> ContT: \ _ -> c x) c

resetT : {{_ : Monad m}} -> ContT r m r -> ContT r' m r
resetT = lift <<< evalContT

shiftT : {{_ : Monad m}} -> ((a -> m r) -> ContT r m r) -> ContT r m a
shiftT f = ContT: (evalContT <<< f)

liftLocal : {{_ : Monad m}}
  -> m r' -> ((r' -> r') -> m r -> m r)
  -> (r' -> r') -> ContT r m ~> ContT r m
liftLocal ask local f (ContT: m) = ContT: \ c -> do
  r <- ask
  local f (m (local (const r) <<< c))
