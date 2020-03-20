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
  functorContT : Functor (ContT R M)
  functorContT .map f m = ContT: \ c -> ContT.run m (c <<< f)

  applicativeContT : Applicative (ContT R M)
  applicativeContT .pure x = ContT: (_$ x)
  applicativeContT ._<*>_ f v =
    ContT: \ c -> ContT.run f $ \ g -> ContT.run v (c <<< g)

  monadContT : Monad (ContT R M)
  monadContT ._>>=_ m k = ContT: $ \ c -> ContT.run m (\ x -> ContT.run (k x) c)

  monadTransContT : MonadTrans (ContT R)
  monadTransContT .lift m = ContT: (m >>=_)
  monadTransContT .transform = monadContT

  monadContContT : MonadCont (ContT R M)
  monadContContT .callCC f =
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
