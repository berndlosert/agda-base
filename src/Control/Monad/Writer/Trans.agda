{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer.Trans where

open import Prelude

open import Control.Monad.Base
open import Control.Monad.Morph
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class

private
  variable
    A B W W' : Set
    M N : Set -> Set

record WriterT (W : Set) (M : Set -> Set) (A : Set) : Set where
  constructor writerT:
  field runWriterT : M (A * W)

open WriterT public

execWriterT : {{_ : Monad M}} -> WriterT W M A -> M W
execWriterT (writerT: m) = do
  (_ , w) <- m
  return w

mapWriterT : (M (A * W) -> N (B * W'))
  -> WriterT W M A -> WriterT W' N B
mapWriterT f (writerT: m) = writerT: (f m)

instance
  functorWriterT : {{_ : Functor M}} -> Functor (WriterT W M)
  functorWriterT .map f = mapWriterT (map (first f))

  applicativeWriterT : {{_ : Monoid W}} {{_ : Applicative M}}
    -> Applicative (WriterT W M)
  applicativeWriterT .pure a = writerT: $ pure (a , neutral)
  applicativeWriterT ._<*>_ (writerT: f) (writerT: x) = writerT: (| k f x |)
    where
      k : _
      k (f , w) (x , w') = (f x , w <> w')

  monadWriterT : {{_ : Monoid W}} {{_ : Monad M}} -> Monad (WriterT W M)
  monadWriterT ._>>=_ (writerT: m) k = writerT: do
    (a , w) <- m
    (b , w') <- runWriterT (k a)
    return (b , w <> w')

  mfunctorWriterT : MFunctor (WriterT W)
  mfunctorWriterT .hoist f = mapWriterT f

  monadTransWriterT : {{_ : Monoid W}} -> MonadTrans (WriterT W)
  monadTransWriterT .lift m = writerT: do
    a <- m
    return (a , neutral)
  monadTransWriterT .tmap f _ = hoist f

  mmonadWriterT : {{_ : Monoid W}} -> MMonad (WriterT W)
  mmonadWriterT .embed k (writerT: m) = writerT: do
    ((a , w) , w') <- runWriterT (k m)
    return (a , w <> w')

  monadWriterWriterT : {{_ : Monoid W}} {{_ : Monad M}}
    -> MonadWriter W (WriterT W M)
  monadWriterWriterT .tell w = writerT: (return (unit , w))
  monadWriterWriterT .listen (writerT: m) = writerT: do
    (a , w) <- m
    return ((a , w) , w)
  monadWriterWriterT .pass (writerT: m) = writerT: do
    ((a , f) , w) <- m
    return (a , f w)

  monadBaseWriterT : {{_ : Monad M}} {{_ : Monad N}} {{_ : MonadBase M N}}
    -> {{_ : Monoid W}} -> MonadBase M (WriterT W N)
  monadBaseWriterT .liftBase m = lift (liftBase m)
