{-# OPTIONS --type-in-type #-}

module Control.Monad.State.Trans where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Control.Monad.IO.Class
open import Control.Monad.Morph
open import Control.Monad.Except.Class
open import Control.Monad.State.Class
open import Control.Monad.Trans.Class

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Control.Monad.Morph public
open Control.Monad.State.Class public
open Control.Monad.Trans.Class public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b e s : Set
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

  MFunctor-StateT : MFunctor (StateT s)
  MFunctor-StateT .hoist f = mapStateT f

  MonadState-StateT : {{_ : Monad m}} -> MonadState s (StateT s m)
  MonadState-StateT .state f = StateT: (return <<< f)

  MonadTrans-StateT : MonadTrans (StateT s)
  MonadTrans-StateT .lift m = StateT: \ s -> do
    a <- m
    return (a , s)

  MonadIO-StateT : {{_ : MonadIO m}} -> MonadIO (StateT s m)
  MonadIO-StateT .liftIO = lift <<< liftIO

  MonadThrow-StateT : {{_ : MonadThrow e m}} -> MonadThrow e (StateT s m)
  MonadThrow-StateT .throw = lift <<< throw

  MonadExcept-StateT : {{_ : MonadExcept e m}} -> MonadExcept e (StateT s m)
  MonadExcept-StateT .catch m h = StateT: \ s ->
    catch (runStateT m s) (\ e -> runStateT (h e) s)
