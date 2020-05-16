{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Morph
open import Control.Monad.Reader.Class
open import Control.Monad.Trans.Class

private
  variable
    A B R R' : Set
    M N : Set -> Set

record ReaderT (R : Set) (M : Set -> Set) (A : Set) : Set where
  constructor readerT:
  field runReaderT : R -> M A

open ReaderT public

mapReaderT : (M A -> N B) -> ReaderT R M A -> ReaderT R N B
mapReaderT f (readerT: m) = readerT: (f ∘ m)

withReaderT : (R' -> R) -> ReaderT R M ~> ReaderT R' M
withReaderT f (readerT: m) = readerT: (m ∘ f)

instance
  functorReaderT : {{_ : Functor M}} -> Functor (ReaderT R M)
  functorReaderT .map f = mapReaderT (map f)

  applicativeReaderT : {{_ : Applicative M}} -> Applicative (ReaderT R M)
  applicativeReaderT .pure = readerT: ∘ const ∘ pure
  applicativeReaderT ._<*>_ (readerT: f) (readerT: x) = readerT: λ r ->
    f r <*> x r

  monadReaderT : {{_ : Monad M}} -> Monad (ReaderT R M)
  monadReaderT ._>>=_ (readerT: m) k = readerT: λ r -> do
    a <- m r
    runReaderT (k a) r

  monadReaderReaderT : {{_ : Monad M}} -> MonadReader R (ReaderT R M)
  monadReaderReaderT .ask = readerT: return
  monadReaderReaderT .local f = withReaderT f

  mfunctorReaderT : MFunctor (ReaderT R)
  mfunctorReaderT .hoist t = mapReaderT t

  monadTransReaderT : MonadTrans (ReaderT R)
  monadTransReaderT .lift = readerT: ∘ const
  monadTransReaderT .tmap f _ = hoist f

  mmonadReaderT : MMonad (ReaderT R)
  mmonadReaderT .embed k (readerT: f) = readerT: λ r -> runReaderT (k (f r)) r

  monadBaseReaderT : {{_ : Monad M}} {{_ : Monad N}} {{_ : MonadBase M N}}
    -> MonadBase M (ReaderT R N)
  monadBaseReaderT .liftBase m = lift (liftBase m)
