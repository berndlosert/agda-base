{-# OPTIONS --type-in-type #-}

module Control.Monad.Writer.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Exception
open import Control.Monad.Cont.Class
open import Control.Monad.IO.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Trans.Class public
open Control.Monad.Writer.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s w w' : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- WriterT
-------------------------------------------------------------------------------

record WriterT (w : Type) (m : Type -> Type) (a : Type) : Type where
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
  Applicative-WriterT .pure a = WriterT: (pure (a , neutral))
  Applicative-WriterT ._<*>_ (WriterT: f) (WriterT: x) = WriterT: (| k f x |)
    where
      k : _
      k (f , w) (x , w') = (f x , w <> w')

  Alternative-WriterT : {{_ : Monoid w}} {{_ : Alternative m}}
    -> Alternative (WriterT w m)
  Alternative-WriterT .empty = WriterT: empty
  Alternative-WriterT ._<|>_ (WriterT: m) (WriterT: n) = WriterT: (m <|> n)

  Monad-WriterT : {{_ : Monoid w}} {{_ : Monad m}} -> Monad (WriterT w m)
  Monad-WriterT ._>>=_ (WriterT: m) k = WriterT: do
    (a , w) <- m
    (b , w') <- runWriterT (k a)
    return (b , w <> w')

  MonadTrans-WriterT : {{_ : Monoid w}} -> MonadTrans (WriterT w)
  MonadTrans-WriterT .lift m = WriterT: do
    a <- m
    return (a , neutral)

  MonadWriter-WriterT : {{_ : Monoid w}} {{_ : Monad m}}
    -> MonadWriter w (WriterT w m)
  MonadWriter-WriterT .tell w = WriterT: (return (unit , w))
  MonadWriter-WriterT .listen (WriterT: m) = WriterT: do
    (a , w) <- m
    return ((a , w) , w)
  MonadWriter-WriterT .pass (WriterT: m) = WriterT: do
    ((a , f) , w) <- m
    return (a , f w)

  MonadReader-WriterT : {{_ : Monoid w}} {{_ : MonadReader r m}}
    -> MonadReader r (WriterT w m)
  MonadReader-WriterT .ask = lift ask
  MonadReader-WriterT .local f = mapWriterT (local f)

  MonadState-WriterT : {{_ : Monoid w}} {{_ : MonadState s m}}
    -> MonadState s (WriterT w m)
  MonadState-WriterT .state f = lift (state f)

  MonadThrow-WriterT : {{_ : Monoid w}} {{_ : MonadThrow m}}
    -> MonadThrow (WriterT w m)
  MonadThrow-WriterT .throw = lift <<< throw

  MonadCatch-WriterT : {{_ : Monoid w}} {{_ : MonadCatch m}}
    -> MonadCatch (WriterT w m)
  MonadCatch-WriterT .catch m h = WriterT: $
    catch (runWriterT m) (\ e -> runWriterT (h e))

  MonadCont-WriterT : {{_ : Monoid w}} {{_ : MonadCont m}}
    -> MonadCont (WriterT w m)
  MonadCont-WriterT .callCC f = WriterT: $
    callCC \ c -> runWriterT (f (\ a -> WriterT: $ c (a , neutral)))
