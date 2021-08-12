{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader.Trans where

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

open Control.Monad.Reader.Class public
open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r r' s w : Type
    m n : Type -> Type

-------------------------------------------------------------------------------
-- ReaderT
-------------------------------------------------------------------------------

abstract
  ReaderT : (r : Type) (m : Type -> Type) (a : Type) -> Type
  ReaderT r m a = r -> m a

  mkReaderT : (r -> m a) -> ReaderT r m a
  mkReaderT = id

  runReaderT : ReaderT r m a -> r -> m a
  runReaderT = id

liftReaderT : m a -> ReaderT r m a
liftReaderT = mkReaderT <<< const

mapReaderT : (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f m = mkReaderT (f <<< runReaderT m)

withReaderT : (r' -> r) -> ReaderT r m a -> ReaderT r' m a
withReaderT f m = mkReaderT (runReaderT m <<< f)

instance
  Functor-ReaderT : {{Functor m}} -> Functor (ReaderT r m)
  Functor-ReaderT .map f = mapReaderT (map f)

  Applicative-ReaderT : {{Applicative m}} -> Applicative (ReaderT r m)
  Applicative-ReaderT .pure = mkReaderT <<< const <<< pure
  Applicative-ReaderT ._<*>_ f x = mkReaderT \ r ->
    runReaderT f r <*> runReaderT x r

  Alternative-ReaderT : {{Alternative m}} -> Alternative (ReaderT r m)
  Alternative-ReaderT .empty = liftReaderT empty
  Alternative-ReaderT ._<|>_ m n = mkReaderT \ r ->
    runReaderT m r <|> runReaderT n r

  Monad-ReaderT : {{Monad m}} -> Monad (ReaderT r m)
  Monad-ReaderT ._>>=_ m k = mkReaderT \ r -> do
    a <- runReaderT m r
    runReaderT (k a) r

  MonadReader-ReaderT : {{Monad m}} -> MonadReader r (ReaderT r m)
  MonadReader-ReaderT .ask = mkReaderT pure
  MonadReader-ReaderT .local f = withReaderT f

  MonadTrans-ReaderT : MonadTrans (ReaderT r)
  MonadTrans-ReaderT .lift = mkReaderT <<< const

  MonadWriter-ReaderT : {{MonadWriter w m}} -> MonadWriter w (ReaderT r m)
  MonadWriter-ReaderT .tell = lift <<< tell
  MonadWriter-ReaderT .listen = mapReaderT listen
  MonadWriter-ReaderT .pass = mapReaderT pass

  MonadState-ReaderT : {{MonadState s m}} -> MonadState s (ReaderT r m)
  MonadState-ReaderT .state = lift <<< state

  MonadIO-ReaderT : {{MonadIO m}} -> MonadIO (ReaderT r m)
  MonadIO-ReaderT .liftIO = lift <<< liftIO

  MonadThrow-ReaderT : {{MonadThrow m}} -> MonadThrow (ReaderT r m)
  MonadThrow-ReaderT .throw = lift <<< throw

  MonadCatch-ReaderT : {{MonadCatch m}} -> MonadCatch (ReaderT r m)
  MonadCatch-ReaderT .catch m h = mkReaderT \ r ->
    catch (runReaderT m r) (\ e -> runReaderT (h e) r)

  MonadCont-ReaderT : {{MonadCont m}} -> MonadCont (ReaderT r m)
  MonadCont-ReaderT .callCC f = mkReaderT \ r ->
    callCC \ c -> runReaderT (f (mkReaderT <<< const <<< c)) r
