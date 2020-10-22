{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer.Trans where

open import Prelude

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
  Functor-WriterT : {{_ : Functor m}} -> Functor (WriterT w m)
  Functor-WriterT .map f = mapWriterT (map (lmap f))

  Applicative-WriterT : {{_ : Monoid w}} {{_ : Applicative m}}
    -> Applicative (WriterT w m)
  Applicative-WriterT .pure a = WriterT: (pure (a , mempty))
  Applicative-WriterT ._<*>_ (WriterT: f) (WriterT: x) = WriterT: (| k f x |)
    where
      k : _
      k (f , w) (x , w') = (f x , w <> w')

  Monad-WriterT : {{_ : Monoid w}} {{_ : Monad m}} -> Monad (WriterT w m)
  Monad-WriterT ._>>=_ (WriterT: m) k = WriterT: do
    (a , w) <- m
    (b , w') <- runWriterT (k a)
    return (b , w <> w')

  MFunctor-WriterT : MFunctor (WriterT w)
  MFunctor-WriterT .hoist f = mapWriterT f

  MonadTrans-WriterT : {{_ : Monoid w}} -> MonadTrans (WriterT w)
  MonadTrans-WriterT .lift m = WriterT: do
    a <- m
    return (a , mempty)

  MMonad-WriterT : {{_ : Monoid w}} -> MMonad (WriterT w)
  MMonad-WriterT .embed k (WriterT: m) = WriterT: do
    ((a , w) , w') <- runWriterT (k m)
    return (a , w <> w')

  MonadWriter-WriterT : {{_ : Monoid w}} {{_ : Monad m}}
    -> MonadWriter w (WriterT w m)
  MonadWriter-WriterT .tell w = WriterT: (return (unit , w))
  MonadWriter-WriterT .listen (WriterT: m) = WriterT: do
    (a , w) <- m
    return ((a , w) , w)
  MonadWriter-WriterT .pass (WriterT: m) = WriterT: do
    ((a , f) , w) <- m
    return (a , f w)

  Alternative-WriterT : {{_ : Monoid w}} {{_ : Alternative m}}
    -> Alternative (WriterT w m)
  Alternative-WriterT .empty = WriterT: empty
  Alternative-WriterT ._<|>_ (WriterT: m) (WriterT: n) = WriterT: (m <|> n)
