{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer.Trans where

open import Prelude

open import Control.Monad.Base public
open import Control.Monad.Morph public
open import Control.Monad.Trans.Class public
open import Control.Monad.Writer.Class public

private
  variable
    a b w w' : Set
    m n : Set -> Set

record WriterT (w : Set) (m : Set -> Set) (a : Set) : Set where
  constructor WriterT:
  field runWriterT : m (a * w)

open WriterT public

execWriterT : {{_ : Monad m}} -> WriterT w m a -> m w
execWriterT (WriterT: m) = do
  (_ , w) <- m
  return w

mapWriterT : (m (a * w) -> n (b * w'))
  -> WriterT w m a -> WriterT w' n b
mapWriterT f (WriterT: m) = WriterT: (f m)

instance
  functorWriterT : {{_ : Functor m}} -> Functor (WriterT w m)
  functorWriterT .map f = mapWriterT (map (first f))

  applicativeWriterT : {{_ : Monoid w}} {{_ : Applicative m}}
    -> Applicative (WriterT w m)
  applicativeWriterT .pure a = WriterT: $ pure (a , neutral)
  applicativeWriterT ._<*>_ (WriterT: f) (WriterT: x) = WriterT: (| k f x |)
    where
      k : _
      k (f , w) (x , w') = (f x , w <> w')

  monadWriterT : {{_ : Monoid w}} {{_ : Monad m}} -> Monad (WriterT w m)
  monadWriterT ._>>=_ (WriterT: m) k = WriterT: do
    (a , w) <- m
    (b , w') <- runWriterT (k a)
    return (b , w <> w')

  mfunctorWriterT : MFunctor (WriterT w)
  mfunctorWriterT .hoist f = mapWriterT f

  monadTransWriterT : {{_ : Monoid w}} -> MonadTrans (WriterT w)
  monadTransWriterT .lift m = WriterT: do
    a <- m
    return (a , neutral)

  mmonadWriterT : {{_ : Monoid w}} -> MMonad (WriterT w)
  mmonadWriterT .embed k (WriterT: m) = WriterT: do
    ((a , w) , w') <- runWriterT (k m)
    return (a , w <> w')

  monadWriterWriterT : {{_ : Monoid w}} {{_ : Monad m}}
    -> MonadWriter w (WriterT w m)
  monadWriterWriterT .tell w = WriterT: (return (unit , w))
  monadWriterWriterT .listen (WriterT: m) = WriterT: do
    (a , w) <- m
    return ((a , w) , w)
  monadWriterWriterT .pass (WriterT: m) = WriterT: do
    ((a , f) , w) <- m
    return (a , f w)

  monadBaseWriterT : {{_ : Monad m}} {{_ : Monad n}} {{_ : MonadBase m n}}
    -> {{_ : Monoid w}} -> MonadBase m (WriterT w n)
  monadBaseWriterT .liftBase m = lift (liftBase m)
