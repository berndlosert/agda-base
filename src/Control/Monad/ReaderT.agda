{-# OPTIONS --type-in-type #-}

module Control.Monad.ReaderT where

open import Control.Monad.MonadReader
open import Control.Monad.MonadTrans
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

instance
  functorReaderT : {{_ : Functor M}} -> Functor (ReaderT R M)
  functorReaderT .map f = map' (map f)

  applicativeReaderT : {{_ : Applicative M}} -> Applicative (ReaderT R M)
  applicativeReaderT .pure = ReaderT: <<< const <<< pure
  applicativeReaderT ._<*>_ f v = ReaderT: $ \ r ->
    ReaderT.run f r <*> ReaderT.run v r

  monadReaderT : {{_ : Monad M}} -> Monad (ReaderT R M)
  monadReaderT ._>>=_ m k = ReaderT: $ \ r -> do
    a <- ReaderT.run m r
    ReaderT.run (k a) r

  monadReaderReaderT : {{_ : Monad M}} -> MonadReader R (ReaderT R M)
  monadReaderReaderT = \ where
    .ask -> ReaderT: return
    .local f -> with' f

  monadTransReaderT : MonadTrans (ReaderT R)
  monadTransReaderT .lift = ReaderT: <<< const
  monadTransReaderT .transform = monadReaderT
