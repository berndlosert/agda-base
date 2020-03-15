{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.Cont where

open import Control.Monad.Trans.Class
open import Data.Functor.Identity
open import Prelude

private
  variable
    A B R R' : Set
    F M : Set -> Set

record Cont (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor Cont:
  field
    run : (A -> M R) -> M R

eval : {{_ : Monad M}} -> Cont R M R -> M R
eval m = Cont.run m return

map' : (M R -> M R) -> Cont R M ~> Cont R M
map' f m = Cont: $ f <<< Cont.run m

with' : ((B -> M R) -> (A -> M R)) -> Cont R M A -> Cont R M B
with' f m = Cont: $ Cont.run m <<< f

instance
  Functor:Cont : Functor (Cont R M)
  Functor:Cont .map f m = Cont: \ c -> Cont.run m (c <<< f)

  Applicative:Cont : Applicative (Cont R M)
  Applicative:Cont .pure x = Cont: (_$ x)
  Applicative:Cont ._<*>_ f v =
    Cont: \ c -> Cont.run f $ \ g -> Cont.run v (c <<< g)

  Monad:Cont : Monad (Cont R M)
  Monad:Cont ._>>=_ m k = Cont: $ \ c -> Cont.run m (\ x -> Cont.run (k x) c)

  MonadTrans:Cont : MonadTrans (Cont R)
  MonadTrans:Cont .lift m = Cont: (m >>=_)
  MonadTrans:Cont .transform _ = Monad:Cont

callCC : ((A -> Cont R M B) -> Cont R M A) -> Cont R M A
callCC f = Cont: $ \ c -> Cont.run (f (\ x -> Cont: $ \ _ -> c x)) c

reset : {{_ : Monad M}} -> Cont R M R -> Cont R' M R
reset = lift <<< eval

shift : {{_ : Monad M}} -> ((A -> M R) -> Cont R M R) -> Cont R M A
shift f = Cont: (eval <<< f)

liftLocal : {{_ : Monad M}}
  -> M R' -> ((R' -> R') -> M R -> M R)
  -> (R' -> R') -> Cont R M ~> Cont R M
liftLocal ask local f m = Cont: $ \ c -> do
    r <- ask
    local f (Cont.run m (local (const r) <<< c))

Cont' : Set -> Set -> Set
Cont' R A = Cont R Identity A

cont : ((A -> R) -> R) -> Cont' R A
cont f = Cont: (\ c -> Identity: (f (Identity.run <<< c)))
