{-# OPTIONS --type-in-type #-}

module Control.Monad.ContT where

open import Control.Monad.MonadCont
open import Control.Monad.MonadTrans
open import Prelude

private
  variable
    A B R R' : Set
    F M : Set -> Set

record ContT (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor ContT:
  field
    run : (A -> M R) -> M R

eval : {{_ : Monad M}} -> ContT R M R -> M R
eval m = ContT.run m return

map' : (M R -> M R) -> ContT R M ~> ContT R M
map' f m = ContT: $ f <<< ContT.run m

with' : ((B -> M R) -> (A -> M R)) -> ContT R M A -> ContT R M B
with' f m = ContT: $ ContT.run m <<< f

instance
  Functor:ContT : Functor (ContT R M)
  Functor:ContT .map f m = ContT: \ c -> ContT.run m (c <<< f)

  Applicative:ContT : Applicative (ContT R M)
  Applicative:ContT .pure x = ContT: (_$ x)
  Applicative:ContT ._<*>_ f v =
    ContT: \ c -> ContT.run f $ \ g -> ContT.run v (c <<< g)

  Monad:ContT : Monad (ContT R M)
  Monad:ContT ._>>=_ m k = ContT: $ \ c -> ContT.run m (\ x -> ContT.run (k x) c)

  MonadTrans:ContT : MonadTrans (ContT R)
  MonadTrans:ContT .lift m = ContT: (m >>=_)
  MonadTrans:ContT .transform = Monad:ContT

  MonadCont:ContT : MonadCont (ContT R M)
  MonadCont:ContT .callCC f =
    ContT: $ \ c -> ContT.run (f (\ x -> ContT: $ \ _ -> c x)) c

reset : {{_ : Monad M}} -> ContT R M R -> ContT R' M R
reset = lift <<< eval

shift : {{_ : Monad M}} -> ((A -> M R) -> ContT R M R) -> ContT R M A
shift f = ContT: (eval <<< f)

liftLocal : {{_ : Monad M}}
  -> M R' -> ((R' -> R') -> M R -> M R)
  -> (R' -> R') -> ContT R M ~> ContT R M
liftLocal ask local f m = ContT: $ \ c -> do
    r <- ask
    local f (ContT.run m (local (const r) <<< c))
