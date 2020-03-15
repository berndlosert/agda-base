{-# OPTIONS --type-in-type #-}

module Control.Monad.Trans.ReaderT where

open import Control.Monad.Trans.Classes
open import Prelude

private
  variable
    A B R R' : Set
    M N : Set -> Set

record ReaderT (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor ReaderT:
  field
    run : R -> M A

map' : (M A -> N B) -> ReaderT R M A -> ReaderT R N B
map' f m = ReaderT: $ f <<< ReaderT.run m

with' : (R' -> R) -> ReaderT R M ~> ReaderT R' M
with' f m = ReaderT: $ ReaderT.run m <<< f

lift : M ~> ReaderT R M
lift m = ReaderT: (const m)

instance
  Functor:ReaderT : {{_ : Functor M}} -> Functor (ReaderT R M)
  Functor:ReaderT .map f = map' (map f)

  Applicative:ReaderT : {{_ : Applicative M}} -> Applicative (ReaderT R M)
  Applicative:ReaderT .pure = lift <<< pure
  Applicative:ReaderT ._<*>_ f v = ReaderT: $ \ r ->
    ReaderT.run f r <*> ReaderT.run v r

  Monad:ReaderT : {{_ : Monad M}} -> Monad (ReaderT R M)
  Monad:ReaderT ._>>=_ m k = ReaderT: $ \ r -> do
    a <- ReaderT.run m r
    ReaderT.run (k a) r

  MonadReader:ReaderT : MonadReader (ReaderT R M)
  MonadReader:ReaderT = \ where
    .ask = ReaderT: return
    .local = with'

