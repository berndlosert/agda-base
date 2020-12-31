{-# OPTIONS --type-in-type #-}

module Control.Monad.State.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Monad.Cont.Class
open import Control.Monad.IO.Class
open import Control.Monad.Except.Class
open import Control.Monad.Reader.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class
open import Control.Monad.Writer.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.State.Class public
open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e r s w : Set
    m n : Set -> Set

-------------------------------------------------------------------------------
-- StateT
-------------------------------------------------------------------------------

record StateT (s : Set) (m : Set -> Set) (a : Set) : Set where
  constructor StateT:
  field runStateT : s -> m (a * s)

open StateT public

evalStateT : {{_ : Monad m}} -> StateT s m a -> s -> m a
evalStateT (StateT: m) s = do
  (a , _) <- m s
  return a

execStateT : {{_ : Monad m}} -> StateT s m a -> s -> m s
execStateT (StateT: m) s0 = do
  (_ , s1) <- m s0
  return s1

mapStateT : (m (a * s) -> n (b * s)) -> StateT s m a -> StateT s n b
mapStateT f (StateT: m) = StateT: (f <<< m)

withStateT : (s -> s) -> StateT s m a -> StateT s m a
withStateT f (StateT: m) = StateT: (m <<< f)

instance
  Functor-StateT : {{_ : Functor m}} -> Functor (StateT s m)
  Functor-StateT .map f (StateT: m) = StateT: \ s0 -> map (lmap f) (m s0)

  Applicative-StateT : {{_ : Monad m}} -> Applicative (StateT s m)
  Applicative-StateT .pure a = StateT: \ s -> return (a , s)
  Applicative-StateT ._<*>_ (StateT: f) (StateT: x) = StateT: \ s0 -> do
      (g , s1) <- f s0
      (y , s2) <- x s1
      return (g y , s2)

  Alternative-StateT : {{_ : Alternative m}} {{_ : Monad m}} ->
    Alternative (StateT s m)
  Alternative-StateT .empty = StateT: (const empty)
  Alternative-StateT ._<|>_ (StateT: m) (StateT: n) = StateT: \ s ->
    m s <|> n s

  Monad-StateT : {{_ : Monad m}} -> Monad (StateT s m)
  Monad-StateT ._>>=_ (StateT: m) k = StateT: \ s0 -> do
    (a , s1) <- m s0
    runStateT (k a) s1

  MonadTrans-StateT : MonadTrans (StateT s)
  MonadTrans-StateT .lift m = StateT: \ s -> do
    a <- m
    return (a , s)

  MonadState-StateT : {{_ : Monad m}} -> MonadState s (StateT s m)
  MonadState-StateT .state f = StateT: (return <<< f)

  MonadReader-StateT : {{_ : MonadReader r m}} -> MonadReader r (StateT s m)
  MonadReader-StateT .ask = lift ask
  MonadReader-StateT .local = mapStateT <<< local

  MonadWriter-StateT : {{_ : MonadWriter w m}} -> MonadWriter w (StateT s m)
  MonadWriter-StateT .tell = lift <<< tell
  MonadWriter-StateT .listen (StateT: m) = StateT: \ s -> do
    (x , s' , w) <- listen (m s)
    pure $ (x , w , s')
  MonadWriter-StateT .pass (StateT: m) = StateT: \ s -> pass do
     (x , f , s') <- m s
     pure $ (x , s' , f)

  MonadIO-StateT : {{_ : MonadIO m}} -> MonadIO (StateT s m)
  MonadIO-StateT .liftIO = lift <<< liftIO

  MonadThrow-StateT : {{_ : MonadThrow e m}} -> MonadThrow e (StateT s m)
  MonadThrow-StateT .throw = lift <<< throw

  MonadExcept-StateT : {{_ : MonadExcept e m}} -> MonadExcept e (StateT s m)
  MonadExcept-StateT .catch m h = StateT: \ s ->
    catch (runStateT m s) (\ e -> runStateT (h e) s)

  MonadCont-StateT : {{_ : MonadCont m}} -> MonadCont (StateT s m)
  MonadCont-StateT .callCC f = StateT: \ s ->
    callCC \ c -> runStateT (f (\ a -> StateT: \ _ -> c (a , s))) s
