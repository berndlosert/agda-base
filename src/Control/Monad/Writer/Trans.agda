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
  FunctorWriterT : {{_ : Functor m}} -> Functor (WriterT w m)
  FunctorWriterT .map f = mapWriterT (map (first f))

  ApplicativeWriterT : {{_ : Monoid w}} {{_ : Applicative m}}
    -> Applicative (WriterT w m)
  ApplicativeWriterT .pure a = WriterT: $ pure (a , neutral)
  ApplicativeWriterT ._<*>_ (WriterT: f) (WriterT: x) = WriterT: (| k f x |)
    where
      k : _
      k (f , w) (x , w') = (f x , w <> w')

  MonadWriterT : {{_ : Monoid w}} {{_ : Monad m}} -> Monad (WriterT w m)
  MonadWriterT ._>>=_ (WriterT: m) k = WriterT: do
    (a , w) <- m
    (b , w') <- runWriterT (k a)
    return (b , w <> w')

  MFunctorWriterT : MFunctor (WriterT w)
  MFunctorWriterT .hoist f = mapWriterT f

  MonadTransWriterT : {{_ : Monoid w}} -> MonadTrans (WriterT w)
  MonadTransWriterT .lift m = WriterT: do
    a <- m
    return (a , neutral)

  MMonadWriterT : {{_ : Monoid w}} -> MMonad (WriterT w)
  MMonadWriterT .embed k (WriterT: m) = WriterT: do
    ((a , w) , w') <- runWriterT (k m)
    return (a , w <> w')

  MonadWriterWriterT : {{_ : Monoid w}} {{_ : Monad m}}
    -> MonadWriter w (WriterT w m)
  MonadWriterWriterT .tell w = WriterT: (return (unit , w))
  MonadWriterWriterT .listen (WriterT: m) = WriterT: do
    (a , w) <- m
    return ((a , w) , w)
  MonadWriterWriterT .pass (WriterT: m) = WriterT: do
    ((a , f) , w) <- m
    return (a , f w)

  MonadBaseWriterT : {{_ : Monad m}} {{_ : Monad n}} {{_ : MonadBase m n}}
    -> {{_ : Monoid w}} -> MonadBase m (WriterT w n)
  MonadBaseWriterT .liftBase m = lift (liftBase m)

  AlternativeWriterT : {{_ : Monoid w}} {{_ : Alternative m}}
    -> Alternative (WriterT w m)
  AlternativeWriterT .empty = WriterT: empty
  AlternativeWriterT ._<|>_ (WriterT: m) (WriterT: n) = WriterT: (m <|> n)
