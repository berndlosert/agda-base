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
    a b e r r' s w : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- ReaderT
-------------------------------------------------------------------------------

record ReaderT (r : Set) (m : Set -> Set) (a : Set) : Set where
  constructor ReaderT:
  field runReaderT : r -> m a

open ReaderT public

liftReaderT : m a -> ReaderT r m a
liftReaderT = ReaderT: <<< const

mapReaderT : (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f m = ReaderT: (f <<< runReaderT m)

withReaderT : (r' -> r) -> ReaderT r m a -> ReaderT r' m a
withReaderT f m = ReaderT: (runReaderT m <<< f)

instance
  Functor-ReaderT : {{Functor m}} -> Functor (ReaderT r m)
  Functor-ReaderT .map f = mapReaderT (map f)

  Applicative-ReaderT : {{Applicative m}} -> Applicative (ReaderT r m)
  Applicative-ReaderT .pure = ReaderT: <<< const <<< pure
  Applicative-ReaderT ._<*>_ f x = ReaderT: \ r ->
    runReaderT f r <*> runReaderT x r

  Alternative-ReaderT : {{Alternative m}} -> Alternative (ReaderT r m)
  Alternative-ReaderT .empty = liftReaderT empty
  Alternative-ReaderT ._<|>_ m n = ReaderT: \ r ->
    runReaderT m r <|> runReaderT n r

  Monad-ReaderT : {{Monad m}} -> Monad (ReaderT r m)
  Monad-ReaderT ._>>=_ m k = ReaderT: \ r -> do
    a <- runReaderT m r
    runReaderT (k a) r

  MonadReader-ReaderT : {{Monad m}} -> MonadReader r (ReaderT r m)
  MonadReader-ReaderT .ask = ReaderT: pure
  MonadReader-ReaderT .local f = withReaderT f

  MonadTrans-ReaderT : MonadTrans (ReaderT r)
  MonadTrans-ReaderT .lift = ReaderT: <<< const

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
  MonadCatch-ReaderT .catch m h = ReaderT: \ r ->
    catch (runReaderT m r) (\ e -> runReaderT (h e) r)

  MonadCont-ReaderT : {{MonadCont m}} -> MonadCont (ReaderT r m)
  MonadCont-ReaderT .callCC f = ReaderT: \ r ->
    callCC \ c -> runReaderT (f (ReaderT: <<< const <<< c)) r
